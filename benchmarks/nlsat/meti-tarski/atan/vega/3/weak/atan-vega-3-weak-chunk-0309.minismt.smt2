(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* (- 12) skoZ) (* (- 1) (* skoX skoX)) (* 4 (* skoY skoX)) (* (- 1) (* skoY skoY)) (* (- 2) (* skoY skoZ)) (* (- 2) (* skoX skoZ)) (* (- 1) (* skoZ skoZ)) (* 4 (* skoX skoX skoX)) (* 40 (* skoY skoX skoZ)) (* 8 (* skoX skoX skoZ)) (* 8 (* skoY skoY skoZ)) (* 4 (* skoY skoZ skoZ)) (* 4 (* skoX skoZ skoZ)) (* 4 (* skoY skoY skoY)) (* (- 3) (* skoY skoY skoX skoX)) (* 2 (* skoY skoX skoX skoZ)) (* 2 (* skoY skoY skoX skoZ)) (* 2 (* skoY skoX skoZ skoZ)) (* 12 (* skoY skoY skoX skoX skoX)) (* 12 (* skoY skoY skoY skoX skoX)) (* (- 28) (* skoY skoY skoX skoX skoZ)) (* (- 8) (* skoY skoX skoX skoX skoZ)) (* (- 8) (* skoY skoY skoY skoX skoZ)) (* (- 8) (* skoY skoX skoX skoZ skoZ)) (* (- 8) (* skoY skoY skoX skoZ skoZ)) (* (- 1) (* skoY skoY skoX skoX skoZ skoZ)) (* 4 (* skoY skoY skoX skoX skoX skoZ skoZ)) (* 4 (* skoY skoY skoY skoX skoX skoZ skoZ))) 3) (and (not (<= (* (- 1) skoX) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))
(set-info :status sat)
(check-sat)
