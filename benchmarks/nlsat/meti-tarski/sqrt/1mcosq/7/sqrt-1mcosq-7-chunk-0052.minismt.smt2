(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 360) (* skoY skoY)) (* 30 (* skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY))) (- 720)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 2 skoY) (* (- 1) pi)) 0) (and (<= (* (- 20) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status sat)
(check-sat)
