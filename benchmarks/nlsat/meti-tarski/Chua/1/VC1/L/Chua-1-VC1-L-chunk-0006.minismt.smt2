(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* (- 1770) skoC) (* 689 skoS)) 0) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))
(set-info :status sat)
(check-sat)
