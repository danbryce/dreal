(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (or (not (<= (+ (* (- 11) (* skoX skoY)) (* 5 (* skoX skoX skoY)) (* 5 (* skoX skoY skoY)) (* 5 (* skoX skoX skoY skoY)) (* (- 15) (* skoX skoX skoY skoY skoZ)) (* skoX skoX skoX skoY skoY skoZ) (* skoX skoX skoY skoY skoY skoZ) (* skoX skoX skoX skoY skoY skoY skoZ)) 0)) (not (<= skoZ 1))) (and (or (not (<= skoY 1)) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (or (not (<= skoY 1)) (not (<= skoZ 1)))) (and (or (not (<= skoX 1)) (not (<= skoZ 1))) (and (or (not (<= (+ skoX skoY (* skoX skoY) (* (- 14) (* skoX skoY skoZ)) (* 2 (* skoX skoX skoY skoZ)) (* 2 (* skoX skoY skoY skoZ)) (* 2 (* skoX skoX skoY skoY skoZ))) (- 1))) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (not (<= skoY 1))) (or (not (<= (+ (* (- 11) (* skoX skoY)) (* 5 (* skoX skoX skoY)) (* 5 (* skoX skoY skoZ)) (* 5 (* skoX skoX skoY skoZ)) (* (- 15) (* skoX skoX skoY skoY skoZ)) (* skoX skoX skoX skoY skoY skoZ) (* skoX skoX skoY skoY skoZ skoZ) (* skoX skoX skoX skoY skoY skoZ skoZ)) 0)) (not (<= skoY 1))))))))))
(set-info :status sat)
(check-sat)
