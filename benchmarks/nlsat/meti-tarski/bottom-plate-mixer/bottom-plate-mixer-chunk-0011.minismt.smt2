(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 7383) skoS) (* (- 3400) skoC)) (- 760000)) (and (<= (+ (* 7383 skoS) (* 3400 skoC)) 760000) (and (<= (* 10000000 skoX) 1) (<= (* (- 1) skoX) 0)))))
(set-info :status sat)
(check-sat)
