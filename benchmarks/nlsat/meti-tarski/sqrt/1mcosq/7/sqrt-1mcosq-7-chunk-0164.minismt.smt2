(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoX skoX) 2) (and (<= (+ (* 10461394944000 (* skoY skoY)) (* (- 871782912000) (* skoY skoY skoY skoY)) (* 29059430400 (* skoY skoY skoY skoY skoY skoY)) (* (- 518918400) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 5765760 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 43680) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 240 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) 20922789888000) (and (<= (+ (* (- 43589145600) (* skoY skoY)) (* 3632428800 (* skoY skoY skoY skoY)) (* (- 121080960) (* skoY skoY skoY skoY skoY skoY)) (* 2162160 (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 24024) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 182 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) (- 87178291200)) (and (<= (+ (* 239500800 (* skoY skoY)) (* (- 19958400) (* skoY skoY skoY skoY)) (* 665280 (* skoY skoY skoY skoY skoY skoY)) (* (- 11880) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 132 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) 479001600) (and (<= (+ (* (- 1814400) (* skoY skoY)) (* 151200 (* skoY skoY skoY skoY)) (* (- 5040) (* skoY skoY skoY skoY skoY skoY)) (* 90 (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) (- 3628800)) (and (<= (+ (* (- 360) (* skoY skoY)) (* 30 (* skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY))) (- 720)) (and (<= (* (- 1) (* skoY skoY)) (- 2)) (and (or (not (<= (+ (* (- 1) skoY) (* 10 skoX)) 0)) (or (not (<= (+ skoY (* (- 10) skoX)) 0)) (<= skoY 0))) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (<= (* (- 20) skoX) (- 1)) (and (<= (+ (* 2 skoY) (* (- 1) pi)) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))))))))))
(set-info :status sat)
(check-sat)
