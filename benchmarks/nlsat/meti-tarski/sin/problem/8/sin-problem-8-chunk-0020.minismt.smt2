(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= skoY 0) (and (not (<= (+ (* 6 skoY) (* (- 1) (* skoY skoY skoY))) 0)) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 2) skoY) pi) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))))
(set-info :status unsat)
(check-sat)
