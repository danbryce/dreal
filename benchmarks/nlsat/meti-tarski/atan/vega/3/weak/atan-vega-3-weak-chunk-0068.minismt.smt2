(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (and (not (<= (+ (* 91 skoX) (* 91 skoY) (* 91 skoZ) (* (- 50) (* skoX skoY)) (* (- 50) (* skoX skoX)) (* (- 50) (* skoX skoZ)) (* (- 50) (* skoY skoZ)) (* (- 50) (* skoY skoY)) (* (- 91) (* skoX skoY skoZ)) (* 50 (* skoX skoY skoY skoZ)) (* 50 (* skoX skoX skoY skoZ))) 50)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))
(set-info :status unsat)
(check-sat)
