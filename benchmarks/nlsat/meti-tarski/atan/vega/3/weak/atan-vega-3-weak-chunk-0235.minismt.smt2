(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (* (- 1) (* skoY skoX)) (- 1))) (and (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= (+ (* (- 36) skoZ) (* 9 (* skoY skoX)) (* (- 3) (* skoX skoX)) (* (- 3) (* skoY skoY)) (* 36 (* skoY skoX skoZ)) (* (- 12) (* skoX skoX skoX)) (* (- 36) (* skoY skoY skoX)) (* (- 36) (* skoY skoX skoX)) (* (- 12) (* skoX skoX skoZ)) (* (- 12) (* skoY skoY skoZ)) (* (- 12) (* skoY skoY skoY)) (* 3 (* skoY skoX skoX skoX)) (* 3 (* skoY skoY skoY skoX)) (* (- 1) (* skoY skoY skoX skoX)) (* (- 16) (* skoY skoY skoX skoX skoX)) (* 12 (* skoY skoX skoX skoX skoZ)) (* 12 (* skoY skoY skoY skoX skoZ)) (* (- 4) (* skoY skoY skoX skoX skoZ)) (* (- 16) (* skoY skoY skoY skoX skoX)) (* skoY skoY skoY skoX skoX skoX) (* 4 (* skoY skoY skoY skoX skoX skoX skoZ))) 9)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))
(set-info :status sat)
(check-sat)
