(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 100) (* skoX skoY)) (* 50 (* skoY skoY)) (* 50 (* skoX skoX))) 51)) (and (not (<= (* 2 skoZ) (- 3))) (and (not (<= (* 2 skoY) (- 3))) (and (not (<= (* 2 skoX) (- 3))) (and (not (<= (* (- 2) skoZ) (- 3))) (and (not (<= (* (- 2) skoY) (- 3))) (not (<= (* (- 2) skoX) (- 3))))))))))
(set-info :status sat)
(check-sat)
