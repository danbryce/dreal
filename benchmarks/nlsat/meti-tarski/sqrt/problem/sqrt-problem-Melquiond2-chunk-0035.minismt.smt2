(set-logic QF_NRA)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (= (* skoSXY skoSXY skoSXY skoSXY) 0) (and (not (= (* skoSXY skoSXY skoSXY) 0)) (and (not (= (* skoSXY skoSXY) 0)) (and (not (= skoSXY 0)) (and (= (+ (* (- 1) skoY) (* (- 1) skoX) (* skoSXY skoSXY)) 0) (and (not (<= skoY 1)) (and (not (<= (* 2 skoX) 3)) (and (not (<= skoSXY 0)) (and (not (<= (* (- 1) skoX) (- 2))) (not (<= (* (- 32) skoY) (- 33)))))))))))))
(set-info :status unsat)
(check-sat)
