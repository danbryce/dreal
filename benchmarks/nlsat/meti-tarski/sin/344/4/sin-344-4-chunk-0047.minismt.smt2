(set-logic QF_NRA)
(declare-fun skoW () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 10080) skoW) (* (- 10080) skoY) (* (- 10080) skoX) (* (- 10080) skoZ) (* 2520 (* skoW skoW skoZ)) (* 5040 (* skoW skoX skoZ)) (* 2520 (* skoX skoX skoZ)) (* 5040 (* skoW skoY skoZ)) (* 2520 (* skoY skoY skoZ)) (* 5040 (* skoY skoX skoZ)) (* 2520 (* skoW skoZ skoZ)) (* 2520 (* skoY skoZ skoZ)) (* 2520 (* skoX skoZ skoZ)) (* 1680 (* skoZ skoZ skoZ)) (* 1680 (* skoW skoW skoW)) (* 2520 (* skoW skoW skoX)) (* 2520 (* skoW skoX skoX)) (* 1680 (* skoX skoX skoX)) (* 2520 (* skoW skoW skoY)) (* 5040 (* skoW skoY skoX)) (* 2520 (* skoY skoX skoX)) (* 2520 (* skoW skoY skoY)) (* 1680 (* skoY skoY skoY)) (* 2520 (* skoY skoY skoX)) (* (- 42) (* skoW skoW skoW skoW skoW)) (* skoW skoW skoW skoW skoW skoW skoW)) 0)) (and (not (<= (* (- 1) skoW) (- 3))) (and (not (<= (* (- 1) skoX) (- 3))) (and (not (<= (* (- 1) skoY) (- 3))) (and (not (<= (* (- 1) skoZ) (- 3))) (and (not (<= (* 10 skoW) 1)) (and (not (<= (* 10 skoX) 1)) (and (not (<= (* 10 skoY) 1)) (not (<= (* 10 skoZ) 1)))))))))))
(set-info :status sat)
(check-sat)
