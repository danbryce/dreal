(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* 16620000 skoX) (* (- 76729) (* skoX skoX))) 1200000000)) (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0)))))
(set-info :status unsat)
(check-sat)
