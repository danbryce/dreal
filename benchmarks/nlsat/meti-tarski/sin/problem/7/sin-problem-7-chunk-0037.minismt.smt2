(set-logic QF_NRA)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= skoX 0) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* (- 1) pi) (* 2 skoY)) 0) (and (<= (* (- 1) skoX) 0) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))
(set-info :status sat)
(check-sat)
