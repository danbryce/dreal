(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* (- 10461394944000) (* skoX skoX)) (* 871782912000 (* skoX skoX skoX skoX)) (* (- 29059430400) (* skoX skoX skoX skoX skoX skoX)) (* 518918400 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 5765760) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 43680 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 240) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (- 20922789888000))) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))
(set-info :status sat)
(check-sat)
