(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1440) (* skoY skoY)) (* 420 (* skoY skoY skoY skoY)) (* (- 32) (* skoY skoY skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoY skoY skoY skoY)) 0) (and (not (<= (* (- 1) (* skoY skoY)) (- 2))) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status sat)
(check-sat)
