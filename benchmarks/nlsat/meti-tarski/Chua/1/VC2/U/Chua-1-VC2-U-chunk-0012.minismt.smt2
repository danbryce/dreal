(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 13) skoS) (* 3 skoC)) 0)) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))
(set-info :status sat)
(check-sat)
