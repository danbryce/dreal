(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))
(set-info :status sat)
(check-sat)
