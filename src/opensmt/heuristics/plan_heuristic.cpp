/*********************************************************************
Author: Daniel Bryce <dbryce@sift.net>
        Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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

#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include "plan_heuristic.h"
#include "json11/json11.hpp"
#include "opensmt/egraph/Egraph.h"
#include "opensmt/tsolvers/TSolver.h"
#include "util/logging.h"
#include "colin/RPGBuilder.h"
#include "colin/val/TIM.h"
#include "colin/FFSolver.h"
#include "colin/colintotalordertransformer.h"
#include "colin/globals.h"
#include "colin/lpscheduler.h"
#include "colin/numericanalysis.h"


using std::string;
using std::ifstream;
using std::unordered_set;
using std::ios;
using std::sort;
 
namespace dreal{ 
    
  extern string get_file_contents(const char* filename);
  extern int get_mode(Enode* e);

  void plan_heuristic::initialize(SMTConfig & c, Egraph & egraph, THandler* thandler, vec<Lit> *trl, vec<int> *trl_lim)  {
    DREAL_LOG_INFO << "plan_heuristic::initialize() " << (thandler == NULL);
    m_egraph = &egraph;
    m_config = &c; 
    theory_handler = thandler;
    trail = trl;
    trail_lim = trl_lim;
    m_is_initialized = true; 
    if (c.nra_plan_heuristic.compare("") != 0){
        const string heuristic_string = get_file_contents(c.nra_plan_heuristic.c_str());
        string err;
        auto json = json11::Json::parse(heuristic_string, err);
        //  auto hinfo = json.array_items();


       //   BMC depth
        m_depth = json["steps"].int_value();
        DREAL_LOG_INFO << "plan_heuristic::initialize() #steps = " << m_depth;


        //   get acts
        for (auto a : json["actions"].array_items()){
          m_actions.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Action = " << a.string_value();
        }

        //   get events
        for (auto a : json["events"].array_items()){
          m_events.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Event = " << a.string_value();
        }

        //   get processes
        for (auto a : json["processes"].array_items()){
          m_processes.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Process = " << a.string_value();
        }

        //   get durative_acts
        for (auto a : json["durative_actions"].array_items()){
          m_durative_actions.push_back(a.string_value());
          DREAL_LOG_INFO << "plan_heuristic::initialize() Durative Action = " << a.string_value();
        }

        for (int i = 0; i < m_depth+1; i++){
          map< string, Enode* > * en = new map< string, Enode* >();
          time_process_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_event_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_act_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_duract_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_fact_enodes.push_back(en);

          en = new map< string, Enode* >();
          time_func_enodes.push_back(en);
        }

        time_enodes.assign(static_cast<int>(m_depth+1), NULL);
	
	num_choices_per_happening = m_actions.size() + 3 * m_durative_actions.size();
	choices.assign(num_choices_per_happening*(m_depth+1), NULL);

	DREAL_LOG_DEBUG << "num_choices_per_happening = " << num_choices_per_happening;

	// vector<bool> *first_decision = new vector<bool>();
	// first_decision->push_back(true);
	// first_decision->push_back(false);
	// m_decision_stack.push_back(new pair<Enode*, vector<bool>*>( ,first_decision));

  Planner::FF::steepestDescent = false;
    Planner::FF::incrementalExpansion = false;
    Planner::FF::invariantRPG = false;
    Planner::FF::timeWAStar = false;
    Planner::LPScheduler::hybridBFLP = false;
    Planner::FF::useDominanceConstraintsInStateHash = true;
    Planner::LPScheduler::hybridBFLP = true;

    Planner::Globals::totalOrder = true;
    Planner::RPGBuilder::modifiedRPG = false;
    Planner::FF::tsChecking = true;
    bool postHocScheduleToMetric = false;
    Planner::LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction = true;


     char* argv[] = { (char*)m_config->nra_plan_domain.c_str(),
		     (char*)m_config->nra_plan_problem.c_str()};
    //int argcount = 2;

    DREAL_LOG_DEBUG << "plan_heuristic::getColinHeuristic() TIM Analysis";
    TIM::performTIMAnalysis(&argv[0]);

    Planner::MinimalState::setTransformer(new Planner::TotalOrderTransformer());

    const bool realOpt =  Planner::Globals::optimiseSolutionQuality;
     Planner::Globals::optimiseSolutionQuality = (Planner::Globals::optimiseSolutionQuality || postHocScheduleToMetric);
   
    DREAL_LOG_DEBUG << "plan_heuristic::getColinHeuristic() Initializing"; 
    // Planner::Globals::writeableVerbosity = 16;
    Planner::RPGBuilder::initialise();

     Planner::Globals::optimiseSolutionQuality = realOpt;

    {
        list<Literal*>::iterator gsItr = Planner::RPGBuilder::getLiteralGoals().begin();
        const list<Literal*>::iterator gsEnd = Planner::RPGBuilder::getLiteralGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            pair<bool, bool> & currStatic = Planner::RPGBuilder::isStatic(*gsItr);
            if (currStatic.first) {
                if (!currStatic.second) {
                    cout << "Static goal " << *(*gsItr) << " resolves to false: no plan can solve this problem\n";
                    //reachedGoal = false;
                    //return workingBestSolution;
                }
            } else {
                goals.insert((*gsItr)->getStateID());
            }

        }

    }
    {
      list<pair<int, int> >::iterator gsItr = Planner::RPGBuilder::getNumericRPGGoals().begin();
        const list<pair<int, int> >::iterator gsEnd = Planner::RPGBuilder::getNumericRPGGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            if (gsItr->first != -1) {
                numericGoals.insert(gsItr->first);
            }
            if (gsItr->second != -1) {
                numericGoals.insert(gsItr->second);
            }
        }
    }


    bool reachesGoals;
    
    Planner::FF::getMyHeuristic(reachesGoals);

    DREAL_LOG_DEBUG << "plan_heuristic::initialize() done"; 
    }
}

void plan_heuristic::inform(Enode * e){
  if (m_atoms.find(e) != m_atoms.end())
    return;
  m_atoms.insert(e);

  DREAL_LOG_INFO << "plan_heuristic::inform(): " << e << endl;
  if (!e->isTAtom() && !e->isNot()){
    unordered_set<Enode *> const & vars = e->get_vars();
    unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      // if (var.find("process") != string::npos) {
      //   int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
      //   int spos = var.find_first_of("_")+1;
      //   int epos = var.find_last_of("_")-1;
      //   string proc = var.substr(spos, epos-spos).c_str();

      //   //  for (auto const & c : consts) {
      //   //    stringstream css;
      //   //    css << c;
      //   //    int cs = atoi(css.str().c_str());
      //   //    if (cs == 1){
      //       DREAL_LOG_INFO << "process = " << proc << " time = " << time << endl;
      //       (*time_process_enodes[time])[proc] = e;
      //       process_enodes.insert(e);
      //       //          }
      //       //         }
      // } else  if (var.find("event") != string::npos) {
      //   int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
      //   int spos = var.find_first_of("_")+1;
      //   int epos = var.find_last_of("_")-1;
      //   string proc = var.substr(spos, epos-spos).c_str();

      //   //  for (auto const & c : consts) {
      //   //    stringstream css;
      //   //    css << c;
      //   //    int cs = atoi(css.str().c_str());
      //   //    if (cs == 1){
      //       DREAL_LOG_INFO << "event = " << proc << " time = " << time << endl;
      //       (*time_event_enodes[time])[proc] = e;
      //       event_enodes.insert(e);
      //   //    }
      //   //  }
      // } else 
      if (var.find("act") == 0) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_")-1;
        string proc = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "action = " << proc << " time = " << time << endl;
            (*time_act_enodes[time])[proc] = e;
            act_enodes.insert(e);
	    int choice = getChoiceIndex(e);
	    DREAL_LOG_INFO << "index = " << choice;
	    choices[num_choices_per_happening*(time)+choice] = e;

        //    }
        //  }
      } else  if (var.find("duract") == 0) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_");
        string proc = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "durative action = " << proc << " time = " << time << endl;
            (*time_duract_enodes[time])[proc] = e;
            duract_enodes.insert(e);
	    int choice = getChoiceIndex(e);
	    DREAL_LOG_INFO << "index = " << choice;
	    choices[num_choices_per_happening*(time)+choice] = e;
        //    }
        //  }
      } else  if (var.find("fact") == 0) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_");
        string fact = var.substr(spos, epos-spos).c_str();

        //  for (auto const & c : consts) {
        //    stringstream css;
        //    css << c;
        //    int cs = atoi(css.str().c_str());
        //    if (cs == 1){
            DREAL_LOG_INFO << "fact = " << fact << " time = " << time << endl;
            (*time_fact_enodes[time])[fact] = e;
            //duract_enodes.insert(e);
	    //int choice = getChoiceIndex(e);
	    //DREAL_LOG_INFO << "index = " << choice;
	    //choices[num_choices_per_happening*(time)+choice] = e;
        //    }
        //  }
      }
    }
  } else if (e->isEq()){
    unordered_set<Enode *> const & vars = e->get_vars();
    unordered_set<Enode *> const & consts = e->get_constants();
    for (auto const & v : vars) {
      stringstream ss;
      ss << v;
      string var = ss.str();
      if (var.find("time") != string::npos) {
        int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        for (auto const & c : consts) {
          stringstream css;
          css << c;
          int cs = atoi(css.str().c_str());
          if (cs == 0){ //  only care about assinging time if wait is possible
            DREAL_LOG_INFO << "time time = " << time << endl;
            time_enodes[time] = e;
          }
        }
      } else if (var.find("func") == 0) {
	int time = atoi(var.substr(var.find_last_of("_")+1).c_str());
        int spos = var.find_first_of("_")+1;
        int epos = var.find_last_of("_")-2;
        string func = var.substr(spos, epos-spos).c_str();
	DREAL_LOG_INFO << "func = " << func << " time = " << time << endl;
	(*time_func_enodes[time])[func] = e;
      }
    }
  }
}

  int plan_heuristic::getChoiceIndex(Enode *e){
    int index = -1;
    map<Enode*, int>::iterator i = choice_indices.find(e);
    if(i == choice_indices.end()){
      DREAL_LOG_INFO << "Generating new time choice index for " << e;
      unordered_set<Enode *> const & vars = e->get_vars();
      for (auto const & v : vars) {
	stringstream ss;
	ss << v;
	string var = ss.str();
	if (var.find("duract_") != string::npos || 
	    var.find("act_") != string::npos) {
	  
	  int spos = var.find_first_of("_")+1;
	  int epos = var.find_last_of("_")-1;
	  string proc = var.substr(spos, epos-spos).c_str();
	  map<string, int>::iterator j = schoice_indices.find(proc);
	  if(j == schoice_indices.end()){
	    DREAL_LOG_INFO << "Generating new choice index for " << e;
	    index = choice_index++;
	    schoice_indices[proc] = index;
	    break;
	  } else {
	    index = (*j).second;	   
	    break;
	  }	  	  
	}
      }
      assert(index >= 0);
      choice_indices[e] = index;
      return index;
    } else {
      return (*i).second;
    }
  }

  // Lit plan_heuristic::getSuggestion(){
  //   DREAL_LOG_INFO << "plan_heuristic::getSuggestion()";
  //   if (!m_is_initialized || m_suggestions.empty()){
  //     getSuggestions();
  //   }
  //   if (!m_suggestions.empty()){
  //     std::pair<Enode *, bool> *s = m_suggestions.back();
  //     m_suggestions.pop_back();
  //     Enode *e = s->first;


  //   if ( e == NULL )
  //     return lit_Undef;



  //   DREAL_LOG_INFO << "plan_heuristic::getSuggestion() " << e;
  //   if (theory_handler == NULL)
  //     DREAL_LOG_INFO << "plan_heuristic::getSuggestion() NULL";
  //   Var v = theory_handler->enodeToVar(e);
  //   delete s;
  //   return Lit( v, !s->second );
  //   } else {
  //     return lit_Undef;
  //   
  // }

  void plan_heuristic::backtrack(){
  if(!m_is_initialized){
      return;
    }

    DREAL_LOG_DEBUG << "plan_heuristic::backtrack()";
    for(auto a : m_suggestions){
      delete a;
    }
    m_suggestions.clear();
    backtracked = true;

    lastTrailEnd = trail->size();
    displayTrail();
    displayStack();

    int bt_point = (trail_lim->size() == 0 ? 
		    0 : (m_stack_lim.size() <= trail_lim->size() ? 
			 m_stack.size() : 
			  m_stack_lim[trail_lim->size()]-1));
    DREAL_LOG_DEBUG << "level = " << trail_lim->size() << " pt = " << bt_point;

    while(m_stack_lim.size() > trail_lim->size() && !m_stack_lim.empty()) 
      m_stack_lim.pop_back();

    for (int i = m_stack.size(); i > bt_point+1; i--){
      std::pair<Enode *, bool> *s = m_stack.back();
      m_stack.pop_back();
      stack_literals.erase(s->first);
      delete s;
      lastTrailEnd--;
    }
 displayStack();

  //   DREAL_LOG_DEBUG << "plan_heuristic::backtrack()";
  //   m_suggestions.clear();
  //   lastTrailEnd = trail->size();

  //   for (int i = m_stack.size(); i > (trail->size()-2); i--){
  //     std::pair<Enode *, bool> *s = m_stack.back();
  //     m_stack.pop_back();
  //     stack_literals.erase(s->first);
  //     delete s;
  //     lastTrailEnd--;
  //   }
  //   backtracked = true;
  //   // displayTrail();
  // }

  // void plan_heuristic::assertLits(){
  //   DREAL_LOG_DEBUG << "plan_heuristic::assertLits()";
  //   displayTrail();
  //   getSuggestions();
  }


  void plan_heuristic::pushTrailOnStack(){
    DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() lastTrailEnd = "
                   << lastTrailEnd << " trail->size() = " << trail->size();
    if(trail_lim->size() > m_stack_lim.size() ) //track start of levels after the first level
      m_stack_lim.push_back(m_stack.size());

    for (int i = lastTrailEnd; i < trail->size(); i++){
      Enode *e = theory_handler->varToEnode(var((*trail)[i]));
      bool msign = !sign((*trail)[i]);
      //   DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e;
      // if (process_enodes.find(e) != process_enodes.end()){
      //   DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
      //   m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
      //   stack_literals.insert(e);
      // } else if (event_enodes.find(e) != event_enodes.end()){
      //   DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
      //   m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
      //   stack_literals.insert(e);
      // } else
	if (act_enodes.find(e) != act_enodes.end()){
        DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      } else if (duract_enodes.find(e) != duract_enodes.end()){
        DREAL_LOG_INFO << "plan_heuristic::pushTrailOnStack() " << e << " " << msign;
        m_stack.push_back(new std::pair<Enode *, bool>(e, msign));
        stack_literals.insert(e);
      }
    }
    lastTrailEnd = trail->size();


    displayStack();
  }

  void plan_heuristic::completeSuggestionsForTrail(){
    for(int i = m_decision_stack.size()-1; i < m_decision_stack.size(); i++){
      pair<Enode*, vector<bool>*>* decision = m_decision_stack[i];
      if(decision->first != NULL){
	m_suggestions.push_back(new std::pair<Enode *, bool>(decision->first, decision->second->back()));
      }
    }


    // for (int time = m_depth; time >= 0; time--){
    //   DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() time = " << time;
    //   // // suggest processes
    //   // map<string, Enode*> *process_at_time = time_process_enodes[time];
    //   // for (auto p : *process_at_time){
    //   //   if (stack_literals.find(p.second) == stack_literals.end()){
    //   //     DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //   //     // p.second->setDecPolarity(true);
    //   //     m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
    //   //     m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
    //   //   }
    //   // }

    //   // // suggest events
    //   // map<string, Enode*> *event_at_time = time_event_enodes[time];
    //   // for (auto p : *event_at_time){
    //   //   if (stack_literals.find(p.second) == stack_literals.end()){
    //   //     DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //   //     // p.second->setDecPolarity(false);
    //   //     m_stack.push_back(new std::pair<Enode *, bool>(p.second, false));
    //   //     m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, false));
    //   //   }
    //   // }

    //   // suggest acts
    //   map<string, Enode*> *act_at_time = time_act_enodes[time];
    //   for (auto p : *act_at_time){
    //     if (stack_literals.find(p.second) == stack_literals.end()){
    //       DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //       // p.second->setDecPolarity(true);
    //       m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
    //       m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
    //     }
    //   }


    //   // suggest duracts
    //   map<string, Enode*> *duract_at_time = time_duract_enodes[time];
    //   for (auto p : *duract_at_time){
    //     if (stack_literals.find(p.second) == stack_literals.end()){
    //       DREAL_LOG_INFO << "plan_heuristic::completeSuggestionsForTrail() suggesting = " << p.second;
    //       // p.second->setDecPolarity(true);
    //       m_stack.push_back(new std::pair<Enode *, bool>(p.second, true));
    //       m_suggestions.push_back(new std::pair<Enode *, bool>(p.second, true));
    //     }
    //   }
    // }
  }


// Assume that m_decision_stack matches m_stack
// and need to suggest next decision
bool plan_heuristic::expand_path(){
    DREAL_LOG_INFO << "plan_heuristic::expand_path()" << endl;

    // cannot expand path if out of choices
    if (m_decision_stack.size() == 0 && !first_path)
      return false;

    first_path = false;
    bool found_step = false;
    int steps_to_add = min(1, (num_choices_per_happening*m_depth)-
			   static_cast<int>(m_decision_stack.size()));

    bool no_steps_left = false;

    DREAL_LOG_INFO << "Adding #steps: " << steps_to_add << endl;
    for (int i = 0; i < steps_to_add; ){
      int time =  ((static_cast<int>(m_decision_stack.size()))/
			    num_choices_per_happening)+1;
      int choice = (static_cast<int>(m_decision_stack.size()))%num_choices_per_happening;

      if(time > m_depth){
	return false;
      }

      DREAL_LOG_DEBUG << "time = " << time << " choice = " << choice;

      no_steps_left = (time == m_depth && choice == num_choices_per_happening-1);
      if(no_steps_left)
	break;


      vector<bool> * current_decision = new vector<bool>();

      Enode* current_enode = choices[num_choices_per_happening*time+choice];
      bool found_existing_value = false;

      if (current_enode != NULL) { 
	DREAL_LOG_INFO << "Adding decision at happening " << time << " " << current_enode;
      

	//      vector<bool> current_decision_copy (current_decision->begin(), current_decision->end());
        // prune out choices that are negated in m_stack
      for (auto e : m_stack) {
	if(e->first == current_enode){
	  current_decision->push_back(e->second);
	  found_existing_value = true;
	  break;
	}	
      }
      if(!found_existing_value){
	double before_decision_value = getColinHeuristic(-1); //value if do nothing
	double after_decision_value = getColinHeuristic(choice); //value if do choice
	if(before_decision_value <= after_decision_value){
	  // adding this action does not improve heuristic value
	  current_decision->push_back(false);
	  current_decision->push_back(true);
	} else {
	  // adding this action does improve heuristic value
	  current_decision->push_back(true);
	  current_decision->push_back(false);
	}
	i++; //added a step
	found_step = true;
      }

      if (current_decision->size() == 0){
	DREAL_LOG_INFO << "No decisions left at time " << time << endl;
	return false;
      }
      }
      m_decision_stack.push_back(new pair<Enode*, vector<bool>*>(current_enode, current_decision));

    }

    return found_step || no_steps_left;
      // static_cast<int>(m_decision_stack.size()) ==
      // num_choices_per_happening*(m_depth); // successfully found a full path
}

  // undo choices on m_decision_stack until earliest violated decision
bool plan_heuristic::unwind_path() {
  // vector<int> path;
  // path.assign(num_autom*(m_depth+1), -1);
  // int actual_path_size = 0;
  // for (auto e : m_stack) {
  //   DREAL_LOG_INFO << "Checking path " << e->first << " = " << e->second;
  //   auto i = (*tim_act_enodeserals[a]).find(e->first);
  // 	if (i != (*mode_literals[a]).end()){
  // 	  DREAL_LOG_DEBUG << "setting path[" << (((*i).second->second*num_autom)+(num_autom-a)-1) << "] = "
  // 			   << (*i).second->first;
  // 	  path[((*i).second->second*num_autom)+(num_autom-a-1)] = (*i).second->first;
  // 	  actual_path_size++;
  // 	  break;
  // 	}
  //     }
  //   }

  //int earliest_disagreement = m_decision_stack.size();
  bool need_bt_to_decision = false;
  for(int i = m_decision_stack.size()-1; i >= 0; i--){
    pair<Enode*, vector<bool>*> *decision = m_decision_stack[i];
    
    bool found_decision = false;
    for(int j = m_stack.size()-1; j >= 0; j--){
      pair<Enode*, bool>* sdecision = m_stack[j];
      if(decision->first == sdecision->first){
	found_decision = true;

	//decision disagrees w/ m_stack
	if(sdecision->second != decision->second->back()){
	  //found possibly earliest disagreement, clear decision stack to this point
	  for(int k = m_decision_stack.size()-1; k > i; k--){
	    delete m_decision_stack[k]->second;
	    delete m_decision_stack[k];
	    m_decision_stack.pop_back();
	  }
	  need_bt_to_decision = false; //backtracked over any empty decisions

	  //clear conflicting decision 
	  m_decision_stack[i]->second->pop_back();  
	  if(m_decision_stack[i]->second->empty()){
	    need_bt_to_decision = true;
	  }
	} 	   
      }
    }
  }

  if(need_bt_to_decision){
    //clean up decision stack so that there are no levels with no decisions
    pbacktrack();
  }
 


  // bool paths_agree = true;
  // int agree_depth = 0;
  // for (int j = static_cast<int>(path.size() - 1); j > -1; j--){
  //   DREAL_LOG_INFO << "Path (" << j << ") = " << path[j] << endl;
  //   int stack_index_for_path_index = static_cast<int>(path.size() - j - 1);
  //   if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size()))
  //     DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = a" 
  // 		     << (m_decision_stack[stack_index_for_path_index]->first+1)
  // 		     << " m"
  // 		     << m_decision_stack[stack_index_for_path_index]->second->back();
  //   else
  //     DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = *";

  //   if (stack_index_for_path_index <  static_cast<int>(m_decision_stack.size())){
  //     if (m_decision_stack[stack_index_for_path_index]->second->back() != path[j]){
  // 	if (paths_agree){
  // 	  agree_depth = stack_index_for_path_index-1;
  // 	  DREAL_LOG_INFO << "Last Agreed at: " << agree_depth << endl;
  // 	}
  // 	paths_agree = false;
  //     }
  //   } else{
  //     if (paths_agree){
  // 	agree_depth = stack_index_for_path_index-1;
  // 	DREAL_LOG_INFO << "Last Agreed at: " << agree_depth << endl;
  //     }
  //     paths_agree = false;
  //   }
  // }

  // // only unwind if decision stack needs to be
  // int num_backtrack_steps = m_decision_stack.size() - agree_depth-1; // actual_path_size;
  // DREAL_LOG_DEBUG << "Backtracking, # steps = " << num_backtrack_steps;
  // if (// static_cast<int>(m_decision_stack.size()) > actual_path_size ||
  //     !paths_agree && num_backtrack_steps > 0){

  //   for (int i = 0; i <  num_backtrack_steps; i++){
  //     DREAL_LOG_INFO << "Backtracking " << i << endl;
  //     if (i == num_backtrack_steps-1){
  // 	//choose sibling of at this level if it exists
  // 	int path_index_for_stack_pos = i;//((m_depth+1)*num_autom) - m_decision_stack.size()+1;
  // 	// if SAT solver already chose a sibling, then choose it, otherwise take the last
  // 	if (path[path_index_for_stack_pos] != -1){
  // 	  DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
  // 	  m_decision_stack.back()->second->pop_back();
  // 	  for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
  // 	       e != m_decision_stack.back()->second->end(); ){
  // 	    if (*e == path[path_index_for_stack_pos]){
  // 	      DREAL_LOG_DEBUG << "ReMoving " << *e;
  // 	      m_decision_stack.back()->second->erase(e);
  // 	      e = m_decision_stack.back()->second->begin();
  // 	    } else{
  // 	      e++;
  // 	    }
  // 	  }
  // 	  m_decision_stack.back()->second->push_back(path[path_index_for_stack_pos]);
  // 	} else{
  // 	  m_decision_stack.back()->second->pop_back();
  // 	  if( m_decision_stack.back()->second->empty()){
  // 	    delete m_decision_stack.back()->second;
  // 	    delete m_decision_stack.back();
  // 	    m_decision_stack.pop_back();
  // 	  }
  // 	}
  //     } else {
  // 	  // the parent choice was unassigned too, so this decision no longer needed
  // 	  delete m_decision_stack.back()->second;
  // 	  delete m_decision_stack.back();
  // 	  m_decision_stack.pop_back();
  // 	}

  //     // there is only a decision to backtrack if m_decision_stack.size() > m_depth - i
  //     //if (static_cast<int>(m_decision_stack.size()) > 0){ // ((m_depth+1)*num_autom)-1 - i){
  // 	// if (i == 0){
  // 	//   // remove decision for time zero, which must be initial node
  // 	//   // this is never to blame for the backtrack, but must be backtracked over
  // 	//   delete m_decision_stack.back()->second;
  // 	//   delete m_decision_stack.back();
  // 	//   m_decision_stack.pop_back();
  // 	// } else if (m_decision_stack.back() != NULL &&
  // 	// 	   m_decision_stack.back()->second->size() > 1){
  // 	//   // there is an unexplored sibling at this level
  // 	//   // remove current choice at time and choose a sibling

  // 	//   int path_index_for_stack_pos = ((m_depth+1)*num_autom) - m_decision_stack.size()+1;
  // 	//   // if SAT solver already chose a sibling, then choose it, otherwise take the last
  // 	//   if (path[path_index_for_stack_pos] != -1){
  // 	//     DREAL_LOG_DEBUG << "Moving to back " << path[path_index_for_stack_pos];
  // 	//     m_decision_stack.back()->second->pop_back();
  // 	//     for (vector<int>::iterator e = m_decision_stack.back()->second->begin();
  // 	// 	 e != m_decision_stack.back()->second->end(); ){
  // 	//       if (*e == path[path_index_for_stack_pos]){
  // 	// 	DREAL_LOG_DEBUG << "ReMoving " << *e;
  // 	// 	m_decision_stack.back()->second->erase(e);
  // 	// 	e = m_decision_stack.back()->second->begin();
  // 	//       } else{
  // 	// 	e++;
  // 	//       }
  // 	//     }
  // 	//     m_decision_stack.back()->second->push_back(path[path_index_for_stack_pos]);
  // 	//   } else{
  // 	//     m_decision_stack.back()->second->pop_back();
  // 	//   }
  // 	//   break;
  // 	// } else {
  // 	//   // the parent choice was unassigned too, so this decision no longer needed
  // 	//   delete m_decision_stack.back()->second;
  // 	//   delete m_decision_stack.back();
  // 	//   m_decision_stack.pop_back();
  // 	// }
  //     // }
  //   }
  // }

  // for (int j = static_cast<int>(path.size() - 1); j > -1; j--){
  //   DREAL_LOG_INFO << "Path (" << j << ") = " << path[j] << endl;
  //   int stack_index_for_path_index = static_cast<int>(path.size() - j - 1);
  //   if (stack_index_for_path_index < static_cast<int>(m_decision_stack.size()))
  //     DREAL_LOG_INFO << "Stack(" << stack_index_for_path_index << ") = " 
  // 		     << m_decision_stack[stack_index_for_path_index]->second->back();
  //   else {
  //     DREAL_LOG_INFO << "No choices left!";
  //   }
  // }

  return m_decision_stack.size() > 0;
}

  bool plan_heuristic::pbacktrack(){

    for(int i = m_decision_stack.size()-1; i >= 0; i--){
      pair<Enode*, vector<bool>*> *decision = m_decision_stack[i];
      if(decision->second->size() <= 1){
	delete m_decision_stack[i]->second;
	delete m_decision_stack[i];
	m_decision_stack.pop_back();	    
      } else {
	m_decision_stack[i]->second->pop_back();
	break;
      }
    }

    // //      int num_backtrack_steps = 1; // actual_path_size;
    // bool found_sibling = false;
    // while (!found_sibling && m_decision_stack.size() > 1){
    //   DREAL_LOG_INFO << "Backtracking at level " 
    // 		     << m_decision_stack.size() << endl;
      
    //   if (m_decision_stack.back()->second != NULL &&
    // 	  m_decision_stack.back()->second->size() > 1){
    // 	// there is an unexplored sibling at this level
    // 	// remove current choice at time and choose a sibling
    // 	m_decision_stack.back()->second->pop_back();
    // 	found_sibling = true;
    // 	break;
    //   } else {
    // 	// the parent choice was unassigned too, so this decision no longer needed
    // 	delete m_decision_stack.back()->second;
    // 	delete m_decision_stack.back();
    // 	m_decision_stack.pop_back();
    //   }
    // }

    // DREAL_LOG_DEBUG << "After BT stack:";
    // int i = 0;
    // for (std::size_t time = (m_depth+1)*num_autom ; 
    // 	 time > (m_depth+1)-m_decision_stack.size(); time--) {
    //   DREAL_LOG_DEBUG << "Stack(" << time << ") =" << m_decision_stack[i++]->second->back();
    // }
    return m_decision_stack.size() > 0;
  }



  void plan_heuristic::getSuggestions() {
    if (!m_suggestions.empty()){
      return;
    }
    DREAL_LOG_INFO << "plan_heuristic::getSuggestions()";
    displayTrail();

    
    if (trail->size() > lastTrailEnd)
      pushTrailOnStack();

    bool suggestion_consistent = isStackConsistentWithSuggestion();



  bool found_path = false;
  bool path_possible = true;
  // bool suggest_defaults = true;

   if(!m_suggestions.empty() && suggestion_consistent) {
     return;
   } else if(!suggestion_consistent || backtracked) {
     path_possible = unwind_path();
   }


   while (!found_path && path_possible){
     if (path_possible){
       found_path = expand_path();
     }
     if (!found_path){
       path_possible = pbacktrack();
     }
   }

   if (m_decision_stack.size() == 0)
     return;




    completeSuggestionsForTrail();

  //  for (int time = m_depth; time >= 0; time--){
  //    DREAL_LOG_DEBUG << "Depth = " << time;
  //      for (auto & p : *time_event_enodes[time]){
  //        Enode* ev = p.second;
  //        // ev->setDecPolarity(l_True);
  //        m_suggestions.push_back(ev);
  //      }
  //    }

  //    for (int time = 0; time <= m_depth; time++){
  //      for (auto & p : *time_process_enodes[time]){
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }

  //    for (int time = 0; time <= m_depth; time++){
  //      for (auto & p : *time_act_enodes[time]){
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }
  //    for (int time = 0; time <= m_depth; time++){
  //      for (auto & p : *time_duract_enodes[time]){
  //        Enode* proc = p.second;
  //        // proc->setDecPolarity(l_True);
  //        m_suggestions.push_back(proc);
  //      }
  //    }

      //  for (auto e : m_suggestions) {
    DREAL_LOG_INFO << "plan_heuristic::getSuggestions(): Suggesting ";
      //                   << (e->getPolarity() == l_True ? "     " : "(not ")
      //                   << e
      //                   << (e->getPolarity() == l_True ? "" : ")")
      //                   << " = "
      //                   << (e->getDecPolarity() == l_True ?
      //                       " True" :
      //                       (e->getDecPolarity() == l_False ? " False" : " Unknown"))
      //                   << endl;
      //  }
}
 
  void plan_heuristic::getBooleansAtTime(int time, Planner::LiteralSet& booleans){
    map<string, Enode*> *facts_at_time = time_fact_enodes[time];
    for(map<string, Enode*>::iterator i = facts_at_time->begin(); i != facts_at_time->end(); i++){
      DREAL_LOG_DEBUG << (*i).second;
      if(stack_literals.find((*i).second) != stack_literals.end()){
	DREAL_LOG_DEBUG << "assn";
      }
// if((*i).second->getDecPolarity() == l_True){
      // 	DREAL_LOG_DEBUG << "true";
      // } else if((*i).second->getDecPolarity() == l_False){
      // 	DREAL_LOG_DEBUG << "false";
      // } else {
      // 	DREAL_LOG_DEBUG << "unk";
      // }
    }

  }


  Planner::ExtendedMinimalState* plan_heuristic::populateStateFromStack(vector<double>& reals, Planner::LiteralSet& booleans){
    DREAL_LOG_DEBUG << "plan_heuristic::populateStateFromStack() "; 

    int time =  ((static_cast<int>(m_decision_stack.size()))/
		 num_choices_per_happening)+1;
    getBooleansAtTime(time-1, booleans);

    






    Planner::ExtendedMinimalState *my_state = new Planner::ExtendedMinimalState();

    my_state->getEditableInnerState().setFacts(reals);
    my_state->getEditableInnerState().setFacts(booleans);
       
    for(auto l : booleans){
      l->write(cout); cout<< endl;
    }
    int p = 0;
    for(auto l : reals){
      PNE *my_pne = Planner::RPGBuilder::getPNE(p++);
      my_pne->write(cout); cout << " = " << l << endl;
    }

    DREAL_LOG_DEBUG << "plan_heuristic::populateStateFromStack() end"; 
    return my_state;
  }

   

  int plan_heuristic::getColinHeuristic(int choice){
    DREAL_LOG_DEBUG << "plan_heuristic::getColinHeuristic() "; 
    
    //bool reachesGoals; 
    //Planner::FF::getMyHeuristic(reachesGoals);   
    //SearchQueueItem * const initialSQI; 
    vector<double> reals; 
    Planner::LiteralSet booleans;    
    Planner::ExtendedMinimalState *state = populateStateFromStack(reals,booleans);
    auto_ptr<Planner::SearchQueueItem> node = auto_ptr<Planner::SearchQueueItem>(new Planner::SearchQueueItem(state, false));
    Planner::ExtendedMinimalState * prevState = NULL;
    Planner::ParentData *  incrementalData = NULL; 
    const Planner::ActionSegment  actId; 
    list<Planner::FFEvent> nowList;
    int stepId = -1;
    map<double, list<pair<int, int> > > * justApplied = 0;
    double tilFrom = 0.001;
     DREAL_LOG_DEBUG << "plan_heuristic::getColinHeuristic() Computing Heuristic";  
     // Planner::FF::evaluateState(node, *state, prevState, goals, numericGoals, 
     //  				incrementalData, node->helpfulActions, actId, node->plan)

     Planner::FF::HTrio hvalue = 
       Planner::FF::calculateHeuristic(*state, prevState, goals, numericGoals, 
				       incrementalData, node->helpfulActions, node->plan,
				       nowList, stepId,  false, justApplied, tilFrom);

     DREAL_LOG_DEBUG << "plan_heuristic::getColinHeuristic() value = " 
		     << hvalue.heuristicValue << " makespan = " << hvalue.makespanEstimate; 
     delete state;      
     // DREAL_LOG_DEBUG << "plan_heuristic::getColinHeuristic() end";
     return hvalue.heuristicValue;   
  }

}