(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1) skoZ) (* (- 1) skoY) (* (- 1) skoX)) (- 1)) (and (<= (+ (* 5 skoZ) (* 5 skoY) (* 5 skoX)) (- 32)) (and (not (<= (* 20 skoZ) 1)) (and (not (<= (* 20 skoY) 1)) (and (not (<= (* 20 skoX) 1)) (and (not (<= (* (- 1) skoZ) (- 15))) (and (not (<= (* (- 1) skoY) (- 15))) (not (<= (* (- 1) skoX) (- 15)))))))))))
(set-info :status unsat)
(check-sat)
