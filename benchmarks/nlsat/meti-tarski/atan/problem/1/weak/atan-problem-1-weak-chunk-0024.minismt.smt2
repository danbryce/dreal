(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* 3 skoY) skoZ) 0)) (and (= (+ (* skoZ skoZ) (* (- 80) (* skoX skoX))) 75) (and (= (* skoY skoY) 3) (and (<= skoX 1) (and (<= (* (- 1) skoZ) 0) (and (<= (* (- 1) skoY) 0) (not (<= skoX 0)))))))))
(set-info :status sat)
(check-sat)
