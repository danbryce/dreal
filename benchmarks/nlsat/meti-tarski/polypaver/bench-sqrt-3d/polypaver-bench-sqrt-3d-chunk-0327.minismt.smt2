(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* (- 11) (* skoX skoY)) (* 5 (* skoX skoX skoY)) (* 5 (* skoX skoY skoY)) (* 5 (* skoX skoX skoY skoY)) (* (- 15) (* skoX skoX skoY skoY skoZ)) (* skoX skoX skoX skoY skoY skoZ) (* skoX skoX skoY skoY skoY skoZ) (* skoX skoX skoX skoY skoY skoY skoZ)) 0) (and (<= skoZ 1) (and (or (not (<= (+ (* (- 11) (* skoX skoY)) (* 5 (* skoX skoX skoY)) (* 5 (* skoX skoY skoY)) (* 5 (* skoX skoX skoY skoY)) (* (- 15) (* skoX skoX skoY skoY skoZ)) (* skoX skoX skoX skoY skoY skoZ) (* skoX skoX skoY skoY skoY skoZ) (* skoX skoX skoX skoY skoY skoY skoZ)) 0)) (not (<= skoZ 1))) (and (or (not (<= skoY 1)) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (or (not (<= skoY 1)) (not (<= skoZ 1)))) (and (<= skoZ 2) (and (<= skoY 2) (and (<= skoX 2) (and (<= (* (- 1) skoZ) (- 1)) (and (<= (* (- 1) skoY) (- 1)) (and (<= (* (- 1) skoX) (- 1)) (and (or (not (<= skoX 1)) (not (<= skoZ 1))) (or (not (<= (+ skoX skoY (* skoX skoY) (* (- 14) (* skoX skoY skoZ)) (* 2 (* skoX skoX skoY skoZ)) (* 2 (* skoX skoY skoY skoZ)) (* 2 (* skoX skoX skoY skoY skoZ))) (- 1))) (not (<= skoZ 1))))))))))))))))
(set-info :status unsat)
(check-sat)
