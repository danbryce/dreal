(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoX skoX) (- 3)) (and (not (<= (+ (* 3 (* skoX skoZ)) (* (- 15) (* skoX skoY)) (* (- 8) (* skoX skoX skoX skoY))) 0)) (and (= (+ (* (- 80) (* skoX skoX)) (* skoZ skoZ)) 75) (and (= (* skoY skoY) 3) (and (<= skoX 1) (and (<= (* (- 1) skoZ) 0) (and (<= (* (- 1) skoY) 0) (not (<= skoX 0))))))))))
(set-info :status unsat)
(check-sat)
