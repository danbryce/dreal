(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= skoY 1) (and (<= skoZ 1) (and (not (<= (* (- 1) (* skoZ skoY)) 0)) (and (not (<= skoX 1)) (and (<= skoZ 2) (and (<= skoY 2) (and (<= skoX 2) (and (<= (* (- 1) skoZ) (- 1)) (and (<= (* (- 1) skoY) (- 1)) (<= (* (- 1) skoX) (- 1))))))))))))
(set-info :status unsat)
(check-sat)