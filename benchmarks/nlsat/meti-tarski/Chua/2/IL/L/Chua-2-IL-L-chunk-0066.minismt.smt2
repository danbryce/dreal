(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (and (not (<= skoX 0)) (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0))))))
(set-info :status sat)
(check-sat)
