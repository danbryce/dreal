(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ skoX skoY skoZ (* (- 1) (* skoX skoY skoZ))) 0) (and (not (<= (+ (* 157 skoX) (* 157 skoY) (* 157 skoZ) (* (- 100) (* skoX skoY)) (* (- 100) (* skoX skoX)) (* (- 100) (* skoX skoZ)) (* (- 100) (* skoY skoZ)) (* (- 100) (* skoY skoY)) (* (- 157) (* skoX skoY skoZ)) (* 100 (* skoX skoY skoY skoZ)) (* 100 (* skoX skoX skoY skoZ))) 100)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status unsat)
(check-sat)
