(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* 4 (* skoY skoY skoZ skoZ)) 0)) (and (not (<= (+ (* 2 skoY) (* skoY skoY) (* 4 (* skoY skoX skoZ)) (* 8 (* skoY skoY skoX skoZ)) (* 4 (* skoY skoY skoY skoX skoZ)) (* (- 64) (* skoY skoY skoX skoZ skoZ)) (* 4 (* skoY skoY skoX skoX skoZ skoZ)) (* 8 (* skoY skoY skoY skoX skoX skoZ skoZ)) (* 4 (* skoY skoY skoY skoY skoX skoX skoZ skoZ))) (- 1))) (and (or (not (<= (+ skoY skoX (* skoY skoX) (* (- 14) (* skoY skoX skoZ)) (* 2 (* skoY skoY skoX skoZ)) (* 2 (* skoY skoX skoX skoZ)) (* 2 (* skoY skoY skoX skoX skoZ))) (- 1))) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (or (not (<= skoY 1)) (not (<= skoZ 1)))) (or (not (<= skoY 1)) (not (<= skoZ 1)))))))))
(set-info :status sat)
(check-sat)
