(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* 3400 skoC) (* 7383 skoS)) 760000) (and (<= (* 10000000 skoX) 1) (<= (* (- 1) skoX) 0))))
(set-info :status sat)
(check-sat)
