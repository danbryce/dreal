(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 12) (* skoY skoY)) (* skoY skoY skoY skoY)) (- 24))) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963))))))
(set-info :status sat)
(check-sat)
