(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* (- 20) (* skoY skoY skoY)) (* 20 (* skoY skoX skoX)) (* skoY skoY skoY skoY skoY)) 0) (and (not (<= skoX 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 2 skoY) (* (- 1) pi)) 0) (and (<= (* (- 1) skoX) 0) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status sat)
(check-sat)
