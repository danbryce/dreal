(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* 540 skoY) (* 540 skoX) (* 540 skoZ) (* 84 (* skoX skoX)) (* 84 (* skoY skoY)) (* 168 (* skoY skoX)) (* 168 (* skoY skoZ)) (* 168 (* skoX skoZ)) (* 84 (* skoZ skoZ)) (* 27 (* skoX skoX skoZ)) (* 27 (* skoY skoY skoZ)) (* 54 (* skoY skoX skoZ)) (* 27 (* skoY skoZ skoZ)) (* 27 (* skoX skoZ skoZ)) (* 9 (* skoZ skoZ skoZ)) (* 9 (* skoX skoX skoX)) (* 27 (* skoY skoX skoX)) (* 9 (* skoY skoY skoY)) (* 27 (* skoY skoY skoX))) (- 840)) (and (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ)) (- 2)) (and (<= (+ skoY skoX skoZ) 2) (and (<= skoZ 1) (and (<= skoY 1) (and (<= skoX 1) (and (<= (* (- 1) skoZ) 0) (and (<= (* (- 1) skoY) 0) (<= (* (- 1) skoX) 0))))))))))
(set-info :status unsat)
(check-sat)
