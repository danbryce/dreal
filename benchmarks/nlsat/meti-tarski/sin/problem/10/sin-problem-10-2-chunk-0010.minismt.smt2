(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(assert (and (= (+ (* (- 1) skoX) (* skoS skoS)) 0) (and (<= (* (- 1) skoSP1) 0) (and (<= (* (- 1) skoSM1) 0) (and (<= (* (- 1) skoS) 0) (not (<= (* 5 skoX) 7)))))))
(set-info :status sat)
(check-sat)
