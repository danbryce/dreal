(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (+ (* (- 1) (* skoX skoX)) (* 4 (* skoX skoY)) (* (- 2) (* skoX skoZ)) (* (- 2) (* skoY skoZ)) (* (- 1) (* skoZ skoZ)) (* (- 1) (* skoY skoY)) (* (- 3) (* skoX skoX skoY skoY)) (* 2 (* skoX skoX skoY skoZ)) (* 2 (* skoX skoY skoY skoZ)) (* 2 (* skoX skoY skoZ skoZ)) (* (- 1) (* skoX skoX skoY skoY skoZ skoZ))) 3)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))
(set-info :status unsat)
(check-sat)
