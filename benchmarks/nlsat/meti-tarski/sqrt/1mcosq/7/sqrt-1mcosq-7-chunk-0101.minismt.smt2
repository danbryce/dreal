(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (= skoY 0)) (and (or (not (<= (+ (* (- 1) skoY) (* 10 skoX)) 0)) (not (<= (+ skoY (* (- 10) skoX)) 0))) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))
(set-info :status sat)
(check-sat)
