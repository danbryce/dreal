(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 6) skoY) (* skoY skoY)) (- 12)) (and (<= (+ (* (- 1) skoY) (* (- 1) skoZ) (* (- 1) skoX)) (- 2)) (and (<= (+ skoY skoZ skoX) 2) (and (<= skoZ 1) (and (<= skoY 1) (and (<= skoX 1) (and (<= (* (- 1) skoZ) 0) (and (<= (* (- 1) skoY) 0) (<= (* (- 1) skoX) 0))))))))))
(set-info :status unsat)
(check-sat)
