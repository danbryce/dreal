(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 360) (* skoY skoY)) (* 30 (* skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY))) (- 720))) (and (not (<= (+ (* 1440 (* skoY skoY)) (* (- 420) (* skoY skoY skoY skoY)) (* 32 (* skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY))) 0)) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))
(set-info :status sat)
(check-sat)
