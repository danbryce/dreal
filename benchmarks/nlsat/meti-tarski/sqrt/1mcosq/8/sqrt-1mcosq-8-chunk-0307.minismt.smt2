(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* 12 (* skoY skoY)) (* (- 1) (* skoY skoY skoY skoY))) 24)) (and (not (<= (+ (* 576 (* skoY skoY)) (* (- 192) (* skoY skoY skoY skoY)) (* 24 (* skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY))) 0)) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
