(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 1) (* skoX skoX)) (* 4 (* skoY skoX)) (* (- 2) (* skoY skoZ)) (* (- 2) (* skoX skoZ)) (* (- 1) (* skoZ skoZ)) (* (- 1) (* skoY skoY)) (* (- 3) (* skoY skoY skoX skoX)) (* 2 (* skoY skoX skoX skoZ)) (* 2 (* skoY skoY skoX skoZ)) (* 2 (* skoY skoX skoZ skoZ)) (* (- 1) (* skoY skoY skoX skoX skoZ skoZ))) 3)) (and (not (<= (+ (* 12 skoZ) (* skoX skoX) (* (- 4) (* skoY skoX)) (* 2 (* skoY skoZ)) (* 2 (* skoX skoZ)) (* skoZ skoZ) (* skoY skoY) (* (- 40) (* skoY skoX skoZ)) (* (- 4) (* skoX skoX skoX)) (* (- 8) (* skoX skoX skoZ)) (* (- 4) (* skoY skoZ skoZ)) (* (- 4) (* skoX skoZ skoZ)) (* (- 8) (* skoY skoY skoZ)) (* (- 4) (* skoY skoY skoY)) (* 3 (* skoY skoY skoX skoX)) (* (- 2) (* skoY skoX skoX skoZ)) (* (- 2) (* skoY skoY skoX skoZ)) (* (- 2) (* skoY skoX skoZ skoZ)) (* 28 (* skoY skoY skoX skoX skoZ)) (* (- 12) (* skoY skoY skoY skoX skoX)) (* (- 12) (* skoY skoY skoX skoX skoX)) (* 8 (* skoY skoX skoX skoZ skoZ)) (* 8 (* skoY skoY skoX skoZ skoZ)) (* 8 (* skoY skoY skoY skoX skoZ)) (* 8 (* skoY skoX skoX skoX skoZ)) (* skoY skoY skoX skoX skoZ skoZ) (* (- 4) (* skoY skoY skoY skoX skoX skoZ skoZ)) (* (- 4) (* skoY skoY skoX skoX skoX skoZ skoZ))) (- 3))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status unsat)
(check-sat)
