(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* (- 63) skoY) (* (- 63) skoX) (* (- 63) skoZ) (* (- 70) (* skoY skoY skoX)) (* (- 70) (* skoY skoY skoY)) (* 63 (* skoY skoX skoZ)) (* (- 70) (* skoY skoY skoZ)) (* (- 15) (* skoY skoY skoY skoY skoX)) (* 70 (* skoY skoY skoY skoX skoZ)) (* (- 15) (* skoY skoY skoY skoY skoZ)) (* (- 15) (* skoY skoY skoY skoY skoY)) (* 15 (* skoY skoY skoY skoY skoY skoX skoZ))) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))
(set-info :status sat)
(check-sat)
