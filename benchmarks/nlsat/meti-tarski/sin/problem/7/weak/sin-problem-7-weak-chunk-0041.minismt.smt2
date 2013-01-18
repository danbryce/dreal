(set-logic QF_NRA)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (not (<= skoX 0)) (and (not (<= (+ pi (* (- 2) skoY)) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963))))))))
(set-info :status sat)
(check-sat)
