(set-logic QF_NRA)
(declare-fun skoB () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* (- 3) (* skoB skoB)) 0)) (and (not (<= skoA 0)) (and (not (<= skoB 0)) (not (<= skoX 0))))))
(set-info :status unsat)
(check-sat)
