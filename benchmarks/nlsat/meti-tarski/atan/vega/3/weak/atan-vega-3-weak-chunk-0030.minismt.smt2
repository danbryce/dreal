(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (not (<= (* (- 1) (* skoX skoY)) (- 1))) (and (not (<= (+ (* (- 4) skoZ) (* skoX skoY) (* 4 (* skoX skoY skoZ)) (* (- 4) (* skoX skoY skoY)) (* (- 4) (* skoX skoX skoY))) 1)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status unsat)
(check-sat)
