(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* (- 3) (* skoY skoX)) (* skoY skoY) (* (- 1) (* skoY skoY skoY skoX))) (- 3)) (and (<= (+ (* 3 (* skoY skoX)) (* (- 1) (* skoY skoY)) (* skoY skoY skoY skoX)) 3) (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* (- 12) skoX) (* (- 12) skoZ) (* 3 (* skoY skoX)) (* (- 1) (* skoY skoY)) (* (- 16) (* skoY skoY skoX)) (* 12 (* skoY skoX skoZ)) (* (- 4) (* skoY skoY skoZ)) (* (- 4) (* skoY skoY skoY)) (* skoY skoY skoY skoX) (* 4 (* skoY skoY skoY skoX skoZ))) 3)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))
(set-info :status unsat)
(check-sat)
