(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* (- 1037836800) (* skoY skoY skoX)) (* 1037836800 (* skoX skoX skoX)) (* 51891840 (* skoY skoY skoY skoY skoX)) (* (- 51891840) (* skoX skoX skoX skoX skoX)) (* (- 1235520) (* skoY skoY skoY skoY skoY skoY skoX)) (* 1235520 (* skoX skoX skoX skoX skoX skoX skoX)) (* 17160 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX)) (* (- 17160) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 156) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX)) (* 156 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX)) 0) (and (not (<= (+ (* (- 6652800) (* skoY skoY skoX)) (* 6652800 (* skoX skoX skoX)) (* 332640 (* skoY skoY skoY skoY skoX)) (* (- 332640) (* skoX skoX skoX skoX skoX)) (* (- 7920) (* skoY skoY skoY skoY skoY skoY skoX)) (* 7920 (* skoX skoX skoX skoX skoX skoX skoX)) (* 110 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX)) (* (- 110) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (not (<= (+ (* (- 60480) (* skoY skoY skoY)) (* 60480 (* skoY skoX skoX)) (* 3024 (* skoY skoY skoY skoY skoY)) (* (- 3024) (* skoY skoX skoX skoX skoX)) (* (- 72) (* skoY skoY skoY skoY skoY skoY skoY)) (* 72 (* skoY skoX skoX skoX skoX skoX skoX)) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY)) 0)) (and (not (<= (+ (* (- 840) (* skoY skoY skoX)) (* 840 (* skoX skoX skoX)) (* 42 (* skoY skoY skoY skoY skoX)) (* (- 42) (* skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (not (<= (+ (* (- 20) (* skoY skoY skoY)) (* 20 (* skoY skoX skoX)) (* skoY skoY skoY skoY skoY)) 0)) (and (not (<= skoX 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 2 skoY) (* (- 1) pi)) 0) (and (<= (* (- 1) skoX) 0) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))))
(set-info :status sat)
(check-sat)
