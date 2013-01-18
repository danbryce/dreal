(set-logic QF_NRA)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (= skoX 0) (and (not (<= (+ (* 1000 pi) (* (- 2000) skoY)) 1)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= skoX 0)) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status unsat)
(check-sat)
