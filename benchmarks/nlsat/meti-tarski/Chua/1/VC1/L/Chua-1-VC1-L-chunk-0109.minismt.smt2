(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoX 0)) (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0))))
(set-info :status sat)
(check-sat)
