(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 12 (* skoY skoY)) (* (- 1) (* skoY skoY skoY skoY))) 24) (and (or (not (<= (+ (* (- 1) skoY) (* 10 skoX)) 0)) (or (not (<= (+ skoY (* (- 10) skoX)) 0)) (<= skoY 0))) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (<= (* (- 20) skoX) (- 1)) (and (<= (+ (* 2 skoY) (* (- 1) pi)) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))))
(set-info :status sat)
(check-sat)
