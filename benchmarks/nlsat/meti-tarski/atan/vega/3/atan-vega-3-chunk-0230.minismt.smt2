(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= (+ (* 9 skoZ) (* (- 9) (* skoY skoX skoZ)) (* 3 (* skoX skoX skoX)) (* 9 (* skoY skoY skoX)) (* 9 (* skoY skoX skoX)) (* 3 (* skoX skoX skoZ)) (* 3 (* skoY skoY skoZ)) (* 3 (* skoY skoY skoY)) (* 4 (* skoY skoY skoX skoX skoX)) (* (- 3) (* skoY skoX skoX skoX skoZ)) (* (- 3) (* skoY skoY skoY skoX skoZ)) (* skoY skoY skoX skoX skoZ) (* 4 (* skoY skoY skoY skoX skoX)) (* (- 1) (* skoY skoY skoY skoX skoX skoX skoZ))) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status sat)
(check-sat)
