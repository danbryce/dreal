(set-logic QF_NRA)
(declare-fun skoW () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoW) 0) (and (not (<= (+ (* (- 12) skoW) (* (- 12) skoY) (* (- 12) skoX) (* (- 12) skoZ) (* 3 (* skoW skoW skoZ)) (* 6 (* skoW skoX skoZ)) (* 3 (* skoX skoX skoZ)) (* 6 (* skoW skoY skoZ)) (* 3 (* skoY skoY skoZ)) (* 6 (* skoY skoX skoZ)) (* 3 (* skoW skoZ skoZ)) (* 3 (* skoY skoZ skoZ)) (* 3 (* skoX skoZ skoZ)) (* 2 (* skoZ skoZ skoZ)) (* 2 (* skoW skoW skoW)) (* 3 (* skoW skoW skoX)) (* 3 (* skoW skoX skoX)) (* 2 (* skoX skoX skoX)) (* 3 (* skoW skoW skoY)) (* 6 (* skoW skoY skoX)) (* 3 (* skoY skoX skoX)) (* 3 (* skoW skoY skoY)) (* 2 (* skoY skoY skoY)) (* 3 (* skoY skoY skoX))) 0)) (and (not (<= (* (- 1) skoW) (- 3))) (and (not (<= (* (- 1) skoX) (- 3))) (and (not (<= (* (- 1) skoY) (- 3))) (and (not (<= (* (- 1) skoZ) (- 3))) (and (not (<= (* 10 skoW) 1)) (and (not (<= (* 10 skoX) 1)) (and (not (<= (* 10 skoY) 1)) (not (<= (* 10 skoZ) 1))))))))))))
(set-info :status sat)
(check-sat)
