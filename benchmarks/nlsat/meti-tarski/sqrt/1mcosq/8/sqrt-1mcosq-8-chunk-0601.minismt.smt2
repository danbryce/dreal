(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (+ (* (- 2612736000) (* skoX skoX)) (* 870912000 (* skoX skoX skoX skoX)) (* (- 116121600) (* skoX skoX skoX skoX skoX skoX)) (* 8229600 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 335520) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 8100 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 120) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 0) (and (<= (+ (* (- 5) pi) (* 10 skoY)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))
(set-info :status sat)
(check-sat)
