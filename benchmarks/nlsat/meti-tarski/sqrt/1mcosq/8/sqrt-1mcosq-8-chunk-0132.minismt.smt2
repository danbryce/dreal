(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* 2612736000 (* skoY skoY)) (* (- 870912000) (* skoY skoY skoY skoY)) (* 116121600 (* skoY skoY skoY skoY skoY skoY)) (* (- 8229600) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 335520 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 8100) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 120 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))
(set-info :status sat)
(check-sat)
