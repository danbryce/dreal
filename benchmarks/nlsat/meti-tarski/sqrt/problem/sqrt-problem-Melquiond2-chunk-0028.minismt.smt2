(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(assert (and (<= (+ (* (- 205) skoX) (* 90 skoSXY) (* 36 (* skoX skoX)) (* 72 (* skoX skoSXY))) 0) (and (= (+ (* (- 1) skoX) (* (- 1) skoY) (* skoSXY skoSXY)) 0) (and (not (<= skoY 1)) (and (not (<= (* 2 skoX) 3)) (and (not (<= skoSXY 0)) (and (not (<= (* (- 1) skoX) (- 2))) (not (<= (* (- 32) skoY) (- 33))))))))))
(set-info :status unsat)
(check-sat)
