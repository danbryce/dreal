(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* 12 (* skoY skoX)) (* 9 (* skoX skoX)) (* 10 (* skoY skoY)) (* 18 (* skoY skoZ)) (* 18 (* skoX skoZ)) (* 9 (* skoZ skoZ)) (* 4 (* skoY skoY skoY skoX)) (* 6 (* skoY skoY skoX skoX)) (* (- 12) (* skoY skoY skoX skoZ)) (* (- 18) (* skoY skoX skoX skoZ)) (* 6 (* skoY skoY skoY skoZ)) (* (- 18) (* skoY skoX skoZ skoZ)) (* 3 (* skoY skoY skoZ skoZ)) (* 3 (* skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoX skoX) (* (- 6) (* skoY skoY skoY skoY skoX skoZ)) (* (- 6) (* skoY skoY skoY skoX skoX skoZ)) (* (- 6) (* skoY skoY skoY skoX skoZ skoZ)) (* 9 (* skoY skoY skoX skoX skoZ skoZ)) (* 3 (* skoY skoY skoY skoY skoX skoX skoZ skoZ))) (- 3)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
