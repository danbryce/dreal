(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) (* skoX skoX)) 3) (and (not (<= (* (- 1) skoY) 0)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status sat)
(check-sat)
