(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= skoY 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ (* (- 2) skoY) pi) 0)) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 1) skoX) skoY) 0)) (and (or (not (<= (+ (* 2000 skoX) (* (- 1) skoY)) 0)) (not (<= (+ (* (- 2000) skoX) skoY) 0))) (and (or (not (<= (+ (* (- 3) skoY) (* 1000 (* skoX skoX skoX))) 0)) (<= (+ (* 2000 skoX) (* (- 1) skoY)) 0)) (<= (+ (* (- 2000) skoX) skoY) 0))))))))))
(set-info :status sat)
(check-sat)
