(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* (- 840) (* skoY skoY skoY)) (* 840 (* skoX skoX skoY)) (* 42 (* skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY))) 0)) (and (not (<= (+ (* (- 6652800) (* skoX skoY skoY)) (* 6652800 (* skoX skoX skoX)) (* 332640 (* skoX skoY skoY skoY skoY)) (* (- 332640) (* skoX skoX skoX skoX skoX)) (* (- 7920) (* skoX skoY skoY skoY skoY skoY skoY)) (* 7920 (* skoX skoX skoX skoX skoX skoX skoX)) (* 110 (* skoX skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 110) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (not (<= (+ (* (- 60480) (* skoY skoY skoY)) (* 60480 (* skoX skoX skoY)) (* 3024 (* skoY skoY skoY skoY skoY)) (* (- 3024) (* skoX skoX skoX skoX skoY)) (* (- 72) (* skoY skoY skoY skoY skoY skoY skoY)) (* 72 (* skoX skoX skoX skoX skoX skoX skoY)) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY)) 0)) (and (not (<= (+ (* (- 840) (* skoX skoY skoY)) (* 840 (* skoX skoX skoX)) (* 42 (* skoX skoY skoY skoY skoY)) (* (- 42) (* skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (not (<= (+ (* (- 20) (* skoY skoY skoY)) (* 20 (* skoX skoX skoY)) (* skoY skoY skoY skoY skoY)) 0)) (and (not (<= skoX 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))))
(set-info :status sat)
(check-sat)
