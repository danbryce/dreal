(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (not (<= (+ (* 362880 skoY) (* (- 60480) (* skoY skoY skoY)) (* 3024 (* skoY skoY skoY skoY skoY)) (* (- 72) (* skoY skoY skoY skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY)) 0)) (and (not (<= (+ (* (- 2520) skoY) (* 420 (* skoY skoY skoY)) (* (- 840000) (* skoY skoY skoX)) (* 840000 (* skoX skoX skoX)) (* (- 21) (* skoY skoY skoY skoY skoY)) (* 42000 (* skoY skoY skoY skoY skoX)) (* (- 42000) (* skoX skoX skoX skoX skoX)) (* 1000 (* skoX skoX skoX skoX skoX skoX skoX))) 0)) (and (not (<= (+ (* (- 120) (* skoY skoY)) (* 20 (* skoY skoY skoY skoY)) (* (- 40000) (* skoY skoY skoY skoX)) (* 40000 (* skoY skoX skoX skoX)) (* (- 1) (* skoY skoY skoY skoY skoY skoY)) (* 2000 (* skoY skoY skoY skoY skoY skoX))) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ (* (- 2) skoY) pi) 0)) (and (not (<= skoX 0)) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (or (not (<= (+ (* (- 1) skoY) (* 2000 skoX)) 0)) (not (<= (+ skoY (* (- 2000) skoX)) 0))) (and (or (not (<= (+ (* (- 3) skoY) (* 1000 (* skoX skoX skoX))) 0)) (<= (+ (* (- 1) skoY) (* 2000 skoX)) 0)) (<= (+ skoY (* (- 2000) skoX)) 0)))))))))))))
(set-info :status sat)
(check-sat)
