(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* (- 63) skoY) (* 21000 (* skoX skoX skoX)) (* (- 1050) (* skoX skoX skoX skoX skoX)) (* 25 (* skoX skoX skoX skoX skoX skoX skoX))) 0)) (and (not (<= (+ (* (- 120) (* skoY skoY)) (* (- 40000) (* skoX skoY skoY skoY)) (* 20 (* skoY skoY skoY skoY)) (* 40000 (* skoX skoX skoX skoY)) (* 2000 (* skoX skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY))) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ (* (- 2) skoY) pi) 0)) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 1) skoX) skoY) 0)) (or (not (<= (+ (* 2000 skoX) (* (- 1) skoY)) 0)) (not (<= (+ (* (- 2000) skoX) skoY) 0)))))))))))
(set-info :status sat)
(check-sat)
