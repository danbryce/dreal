(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 10080) skoZ) (* (- 10080) skoY) (* (- 10080) skoX) (* 1680 (* skoZ skoZ skoZ)) (* 2520 (* skoZ skoX skoX)) (* 2520 (* skoZ skoY skoY)) (* 5040 (* skoZ skoY skoX)) (* 2520 (* skoZ skoZ skoY)) (* 2520 (* skoZ skoZ skoX)) (* 1680 (* skoX skoX skoX)) (* 2520 (* skoY skoX skoX)) (* 1680 (* skoY skoY skoY)) (* 2520 (* skoY skoY skoX)) (* (- 42) (* skoZ skoZ skoZ skoZ skoZ)) (* skoZ skoZ skoZ skoZ skoZ skoZ skoZ)) 0) (and (not (<= (* (- 1) skoX) (- 3))) (and (not (<= (* (- 1) skoY) (- 3))) (and (not (<= (* (- 1) skoZ) (- 3))) (and (not (<= (* 10 skoX) 1)) (and (not (<= (* 10 skoY) 1)) (not (<= (* 10 skoZ) 1)))))))))
(set-info :status sat)
(check-sat)
