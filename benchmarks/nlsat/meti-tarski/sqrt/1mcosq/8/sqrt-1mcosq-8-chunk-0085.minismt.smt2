(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 20160) (* skoY skoY)) (* 1680 (* skoY skoY skoY skoY)) (* (- 56) (* skoY skoY skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (- 40320))) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (<= (* (- 10) skoX) (- 1)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2))))))))
(set-info :status sat)
(check-sat)
