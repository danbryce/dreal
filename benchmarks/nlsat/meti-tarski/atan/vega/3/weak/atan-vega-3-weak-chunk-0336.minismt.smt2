(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* (- 3) (* skoX skoX)) (* 12 (* skoY skoX)) (* (- 6) (* skoY skoY)) (* (- 6) (* skoY skoZ)) (* (- 6) (* skoX skoZ)) (* (- 3) (* skoZ skoZ)) (* (- 10) (* skoY skoY skoX skoX)) (* 4 (* skoY skoY skoY skoX)) (* 6 (* skoY skoX skoX skoZ)) (* 4 (* skoY skoY skoX skoZ)) (* (- 2) (* skoY skoY skoY skoZ)) (* 6 (* skoY skoX skoZ skoZ)) (* (- 1) (* skoY skoY skoZ skoZ)) (* (- 1) (* skoY skoY skoY skoY)) (* (- 3) (* skoY skoY skoY skoY skoX skoX)) (* 2 (* skoY skoY skoY skoX skoX skoZ)) (* 2 (* skoY skoY skoY skoY skoX skoZ)) (* (- 3) (* skoY skoY skoX skoX skoZ skoZ)) (* 2 (* skoY skoY skoY skoX skoZ skoZ)) (* (- 1) (* skoY skoY skoY skoY skoX skoX skoZ skoZ))) 9)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status unsat)
(check-sat)
