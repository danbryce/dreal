(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 10461394944000 (* skoY skoY)) (* (- 871782912000) (* skoY skoY skoY skoY)) (* 29059430400 (* skoY skoY skoY skoY skoY skoY)) (* (- 518918400) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 5765760 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 43680) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 240 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) 20922789888000) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status sat)
(check-sat)
