(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* (- 1) skoX) (* (- 2) (* skoX skoX)) (* (- 1) (* skoX skoX skoX))) 0)) (and (= (* skoY skoY) 3) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 1) skoY) 0) (<= (+ (* (- 1) skoX) skoY) 0)))))))
(set-info :status unsat)
(check-sat)
