(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* (- 360) (* skoX skoX)) (* 30 (* skoX skoX skoX skoX)) (* (- 1) (* skoX skoX skoX skoX skoX skoX))) (- 720))) (and (not (<= (+ (* (- 1) skoX) skoY) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963))))))
(set-info :status sat)
(check-sat)
