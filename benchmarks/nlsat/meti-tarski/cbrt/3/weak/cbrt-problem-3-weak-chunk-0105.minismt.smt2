(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 13 skoY) (* 13 skoZ) (* 5 skoX) (* 10 (* skoY skoY)) (* 10 (* skoY skoX)) (* 36 (* skoY skoZ)) (* 10 (* skoZ skoZ)) (* 10 (* skoZ skoX)) (* 20 (* skoY skoY skoZ)) (* 20 (* skoY skoZ skoX)) (* 20 (* skoY skoZ skoZ))) (- 4)) (and (not (<= (* 20 skoZ) 1)) (and (not (<= (* 20 skoY) 1)) (and (not (<= (* 20 skoX) 1)) (and (not (<= (* (- 1) skoZ) (- 15))) (and (not (<= (* (- 1) skoY) (- 15))) (not (<= (* (- 1) skoX) (- 15))))))))))
(set-info :status unsat)
(check-sat)
