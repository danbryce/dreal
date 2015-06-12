/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include <utility>
#include <sstream>
#include <string>
#include <unordered_set>
#include "util/logging.h"
#include "util/interval.h"
#include "util/string.h"
#include "dsolvers/icp_solver.h"
#include "dsolvers/nra_solver.h"

using std::pair;
using std::boolalpha;
using std::unordered_set;

namespace dreal {
nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver (i, n, c, e, t, x, d, s), m_decisions(0) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
}

nra_solver::~nra_solver() { }

// `inform` sets up env (mapping from variables(enode) in literals to their [lb, ub])
lbool nra_solver::inform(Enode * e) {
    unordered_set<Enode *> const & vars = e->get_vars();
    static stringstream ss;
    for (auto const & v : vars) {
        double const lb = v->getLowerBound();
        double const ub = v->getUpperBound();
        m_env.insert(v, interval(lb, ub));
        if (DREAL_LOG_DEBUG_IS_ON) {
            ss << v << " ";
        }
    }
    if (DREAL_LOG_DEBUG_IS_ON) {
        DREAL_LOG_DEBUG << "nra_solver::inform: " << e << " with polarity " << e->getPolarity().toInt()
                        << " vars = { " << ss.str() << "}";
        ss.str(string());
    }
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check"
//
// assertLit adds a literal(e) to stack of asserted literals.
bool nra_solver::assertLit (Enode * e, bool reason) {
    DREAL_LOG_DEBUG << "nra_solver::assertLit: " << e
                    << ", reason: " << boolalpha << reason
                    << ", polarity: " << e->getPolarity().toInt()
                    << ", decPolarity: " << e->getDecPolarity().toInt();
    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        DREAL_LOG_DEBUG << "nra_solver::assertLit: " << e << " is deduced" << e;
        return true;
    }
    m_stack.push_back(e);

    return true;
}

// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint () {
    DREAL_LOG_DEBUG << "nra_solver::pushBacktrackPoint " << m_stack.size();
    m_env.push();
    m_stack.push();
    m_explanation_stack.push();
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint () {
    DREAL_LOG_DEBUG << "nra_solver::popBacktrackPoint";
    m_explanation_stack.pop();
    m_stack.pop();
    m_env.pop();
}

box nra_solver::icp_loop(box b, contractor const & ctc, SMTConfig & config) const {
    vector<box> solns;
    stack<box> box_stack;
    box_stack.push(b);
    do {
        DREAL_LOG_INFO << "icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.top();
        box_stack.pop();
        try {
            b = ctc.prune(b, config);
            if (config.nra_stat) { m_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!b.is_empty()) {
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            if (config.nra_stat) { m_stat.increase_branch(); }
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push(second);
                    box_stack.push(first);
                } else {
                    box_stack.push(first);
                    box_stack.push(second);
                }
                if (config.nra_proof) {
                    config.nra_proof_out << "[branched on "
                                         << b.get_name(i)
                                         << "]" << endl;
                }
            } else {
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
                config.nra_found_soln++;
                if (config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(b, config.nra_found_soln);
                }
                solns.push_back(b);
            }
        }
    } while (box_stack.size() > 0);
    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        return b;
    }
}

box nra_solver::icp_loop_with_ncbt(box b, contractor const & ctc, SMTConfig & config) const {
    static unsigned prune_count = 0;
    stack<box> box_stack;
    stack<int> bisect_var_stack;
    box_stack.push(b);
    bisect_var_stack.push(-1);  // Dummy var
    do {
        // Loop Invariant
        assert(box_stack.size() == bisect_var_stack.size());
        DREAL_LOG_INFO << "new_icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.top();
        try {
            b = ctc.prune(b, config);
            if (config.nra_stat) { m_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        prune_count++;
        box_stack.pop();
        bisect_var_stack.pop();
        if (!b.is_empty()) {
            // SAT
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            if (config.nra_stat) { m_stat.increase_branch(); }
            int const index = get<0>(splits);
            if (index >= 0) {
                config.inc_icp_decisions();
                box const & first    = get<1>(splits);
                box const & second   = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push(second);
                    box_stack.push(first);
                } else {
                    box_stack.push(first);
                    box_stack.push(second);
                }
                bisect_var_stack.push(index);
                bisect_var_stack.push(index);
            } else {
                break;
            }
        } else {
            // UNSAT
            while (box_stack.size() > 0) {
                assert(box_stack.size() == bisect_var_stack.size());
                int bisect_var = bisect_var_stack.top();
                ibex::BitSet const & input = ctc.input();
                DREAL_LOG_DEBUG << ctc;
                if (!input[bisect_var]) {
                    box_stack.pop();
                    bisect_var_stack.pop();
                } else {
                    break;
                }
            }
        }
    } while (box_stack.size() > 0);
    DREAL_LOG_DEBUG << "prune count = " << prune_count;
    return b;
}

void nra_solver::output_solution(box const & b, unsigned i) const {
    if (i > 0) {
        cout << i << "-th ";
    }
    cout << "Solution:" << endl;
    cout << b << endl;
    if (!config.nra_model_out.is_open()) {
        config.nra_model_out.open(config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
        if (config.nra_model_out.fail()) {
            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
            exit(1);
        }
    }
    display(config.nra_model_out, b, false, true);
}

void nra_solver::handle_sat_case(box const & b) const {
    // SAT
    // --proof option
    if (config.nra_proof) {
        config.nra_proof_out.close();
        config.nra_proof_out.open(config.nra_proof_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
        display(config.nra_proof_out, b, !config.nra_readable_proof, true);
    }
    // --model option
    if (config.nra_model && config.nra_multiple_soln == 1) {
        // Only output here when --multiple_soln is not used
        output_solution(b, config);
    }
#ifdef SUPPORT_ODE
    // --visualize option
    if (config.nra_json) {
        json traces = {};
        // Need to run ODE pruning operator once again to generate a trace
        for (constraint * const ctr : m_stack) {
            if (ctr->get_type() == constraint_type::ODE) {
                contractor_capd_fwd_full fwd_full(b, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size);
                json trace = fwd_full.generate_trace(b, config);
                traces.push_back(trace);
            }
        }
        json vis_json;
        vis_json["traces"] = traces;
        config.nra_json_out << vis_json.dump() << endl;;
    }
#endif
    // For API call
    b.assign_to_enode();
    return;
}

void nra_solver::handle_deduction() {
    for (Enode * const l : m_lits) {
        if (l->getPolarity() == l_Undef && !l->isDeduced()) {
            auto it = m_ctr_map.find(make_pair(l, true));
            if (it != m_ctr_map.end()) {
                constraint * ctr = it->second;
                nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
                if (nl_ctr) {
                    pair<lbool, ibex::Interval> p = nl_ctr->eval(m_box);
                    if (p.first == l_False) {
                        // We know that this literal has to be false;
                        l->setDeduced(l_False, id);
                        deductions.push_back(l);
                        DREAL_LOG_INFO << "Deduced: " << *nl_ctr << "\t" << p.first << "\t" << p.second;
                    } else if (p.first == l_True) {
                        // We know that this literal has to be true;
                        l->setDeduced(l_True, id);
                        deductions.push_back(l);
                        DREAL_LOG_INFO << "Deduced: " << *nl_ctr << "\t" << p.first << "\t" << p.second;
                    }
                }
            }
        }
    }
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    DREAL_LOG_INFO << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ")";
    DREAL_LOG_DEBUG << "nra_solver::check: env = ";
    DREAL_LOG_DEBUG << m_env;
    DREAL_LOG_DEBUG << "nra_solver::check: stack = ";
    DREAL_LOG_DEBUG << m_stack;
    DREAL_LOG_DEBUG << "nra_solver::check: explanation_stack = ";
    DREAL_LOG_DEBUG << m_explanation_stack;
    bool result = true;
    icp_solver solver(config, egraph, sstore, m_stack, m_env, complete);
    if (!complete) {
        // Incomplete Check
        result = solver.prop();
    } else {
        // Complete Check
        result = solver.solve();
    }

    for (Enode * const l : solver.get_explanation()) {
        if (find(m_explanation_stack.begin(), m_explanation_stack.end(), l) == m_explanation_stack.end()) {
            m_explanation_stack.push_back(l);
        }
    }

    DREAL_LOG_INFO << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ")"
                   << " result = " << boolalpha << result;
    if (!result) {
        explanation = m_explanation_stack.get_vec();
        if (DREAL_LOG_INFO_IS_ON) {
            DREAL_LOG_INFO << "nra_solver::check: explanation provided: (size = " << explanation.size() << " out of " << m_stack.size() << ")";
            for (Enode * const e : explanation) {
                DREAL_LOG_INFO << "\t" << (e->getPolarity() == l_False ? "!" : "") << e;
            }
        }
    }

    // Print out JSON
#ifdef ODE_ENABLED
    if (complete && result && config.nra_ODE_contain && config.nra_json) {
        solver.print_json(config.nra_json_out);
    }
#endif
    DREAL_LOG_INFO << "============================";
    m_decisions += solver.nsplit();
    return result;
}

// Return true if the enode belongs to this theory. You should examine
// the structure of the node to see if it matches the theory operators
bool nra_solver::belongsToT(Enode * e) {
    (void)e;
    assert(e);
    return true;
}

// Copy the model into enode's data
void nra_solver::computeModel() {
    DREAL_LOG_DEBUG << "nra_solver::computeModel" << endl;
}

#ifdef PRODUCE_PROOF
Enode * nra_solver::getInterpolants() {
    return nullptr;
}
#endif
}
