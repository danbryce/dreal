(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (and (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0) (and (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))
(set-info :status unsat)
(check-sat)
