(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (* skoX skoY) 1)) (and (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* (- 1) (* skoX skoY)) (* skoX skoY skoZ)) (- 1))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status unsat)
(check-sat)
