(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1) skoY) (* (- 1) skoZ) (* (- 1) skoX)) (- 1)) (and (<= (* 2 skoY) (- 1)) (and (not (<= skoZ 0)) (and (not (<= skoY 0)) (not (<= skoX 0)))))))
(set-info :status unsat)
(check-sat)
