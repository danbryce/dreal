(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 1) skoZ) (* (- 1) skoY) (* (- 1) skoX)) 0)) (and (not (<= (* (- 10) skoX) (- 11))) (and (not (<= (* (- 10) skoY) (- 11))) (and (not (<= (* (- 10) skoZ) (- 11))) (and (not (<= (* 10 skoX) 1)) (and (not (<= (* 10 skoY) 1)) (not (<= (* 10 skoZ) 1)))))))))
(set-info :status unsat)
(check-sat)
