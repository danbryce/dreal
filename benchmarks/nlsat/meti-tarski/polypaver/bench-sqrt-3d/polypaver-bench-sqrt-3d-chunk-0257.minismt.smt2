(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) (* skoX skoY skoZ)) 1)) (and (or (not (<= skoY 1)) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (or (not (<= skoY 1)) (not (<= skoZ 1)))) (and (or (not (<= skoX 1)) (not (<= skoZ 1))) (or (not (<= (+ skoX skoY (* skoX skoY) (* (- 14) (* skoX skoY skoZ)) (* 2 (* skoX skoX skoY skoZ)) (* 2 (* skoX skoY skoY skoZ)) (* 2 (* skoX skoX skoY skoY skoZ))) (- 1))) (not (<= skoZ 1))))))))
(set-info :status sat)
(check-sat)
