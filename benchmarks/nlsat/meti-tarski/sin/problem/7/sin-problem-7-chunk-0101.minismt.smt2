(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* (- 120) skoY) (* 20 (* skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY))) 0)) (and (not (<= (+ (* (- 20) (* skoY skoY skoY)) (* 20 (* skoY skoX skoX)) (* skoY skoY skoY skoY skoY)) 0)) (and (not (<= skoX 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
