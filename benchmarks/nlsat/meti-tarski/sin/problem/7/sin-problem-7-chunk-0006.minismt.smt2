(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* 2 skoY) (* (- 1) pi)) 0)) (and (<= (* (- 1) skoX) 0) (not (<= (+ (* (- 1) skoX) skoY) 0)))))
(set-info :status sat)
(check-sat)
