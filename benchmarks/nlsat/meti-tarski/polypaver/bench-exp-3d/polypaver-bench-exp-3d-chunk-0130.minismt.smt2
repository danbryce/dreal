(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 60 skoY) (* 60 skoZ) (* (- 60) skoX) (* 12 (* skoX skoX)) (* (- 48) (* skoY skoY)) (* (- 36) (* skoY skoX)) (* 24 (* skoY skoZ)) (* (- 48) (* skoZ skoZ)) (* (- 36) (* skoZ skoX)) (* (- 1) (* skoX skoX skoX)) (* 9 (* skoY skoX skoX)) (* 11 (* skoY skoY skoY)) (* 21 (* skoY skoY skoX)) (* (- 27) (* skoY skoY skoZ)) (* (- 18) (* skoY skoZ skoX)) (* (- 27) (* skoY skoZ skoZ)) (* 9 (* skoZ skoX skoX)) (* 11 (* skoZ skoZ skoZ)) (* 21 (* skoZ skoZ skoX)) (* (- 1) (* skoY skoX skoX skoX)) (* (- 3) (* skoY skoY skoX skoX)) (* (- 1) (* skoY skoY skoY skoY)) (* (- 3) (* skoY skoY skoY skoX)) (* 6 (* skoY skoZ skoX skoX)) (* 8 (* skoY skoY skoY skoZ)) (* 15 (* skoY skoY skoZ skoX)) (* 18 (* skoY skoY skoZ skoZ)) (* 15 (* skoY skoZ skoZ skoX)) (* 8 (* skoY skoZ skoZ skoZ)) (* (- 1) (* skoZ skoX skoX skoX)) (* (- 3) (* skoZ skoZ skoX skoX)) (* (- 1) (* skoZ skoZ skoZ skoZ)) (* (- 3) (* skoZ skoZ skoZ skoX)) (* (- 1) (* skoY skoZ skoX skoX skoX)) (* (- 3) (* skoY skoY skoZ skoX skoX)) (* (- 1) (* skoY skoY skoY skoY skoZ)) (* (- 3) (* skoY skoY skoY skoZ skoX)) (* (- 3) (* skoY skoZ skoZ skoX skoX)) (* (- 3) (* skoY skoY skoY skoZ skoZ)) (* (- 6) (* skoY skoY skoZ skoZ skoX)) (* (- 3) (* skoY skoY skoZ skoZ skoZ)) (* (- 3) (* skoY skoZ skoZ skoZ skoX)) (* (- 1) (* skoY skoZ skoZ skoZ skoZ))) (- 120)) (and (<= (* (- 1) skoX) 0) (and (<= (* (- 1) skoY) 0) (and (<= (* (- 1) skoZ) 0) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= (+ skoY skoZ skoX) 2) (<= (+ (* (- 1) skoY) (* (- 1) skoZ) (* (- 1) skoX)) (- 2)))))))))))
(set-info :status unsat)
(check-sat)
