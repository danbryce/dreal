(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 4) (* skoY skoY skoZ skoZ)) 0) (and (<= skoZ 1) (and (or (not (<= (+ skoY skoX (* skoY skoX) (* (- 14) (* skoY skoX skoZ)) (* 2 (* skoY skoX skoX skoZ)) (* 2 (* skoY skoY skoX skoZ)) (* 2 (* skoY skoY skoX skoX skoZ))) (- 1))) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (not (<= skoZ 1))) (and (<= (* (- 1) skoX) (- 1)) (and (<= (* (- 1) skoY) (- 1)) (and (<= (* (- 1) skoZ) (- 1)) (and (<= skoX 2) (and (<= skoY 2) (and (<= skoZ 2) (and (or (not (<= skoX 1)) (or (not (<= skoY 1)) (not (<= skoZ 1)))) (or (not (<= skoY 1)) (not (<= skoZ 1)))))))))))))))
(set-info :status sat)
(check-sat)
