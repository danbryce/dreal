(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* (- 3) (* skoX skoX)) (* (- 4) (* skoY skoX)) (* (- 6) (* skoY skoZ)) (* (- 6) (* skoX skoZ)) (* (- 3) (* skoZ skoZ)) (* (- 3) (* skoY skoY)) (* (- 1) (* skoY skoY skoX skoX)) (* 6 (* skoY skoX skoX skoZ)) (* 6 (* skoY skoY skoX skoZ)) (* 6 (* skoY skoX skoZ skoZ)) (* (- 3) (* skoY skoY skoX skoX skoZ skoZ))) 1) (and (not (<= (* (- 1) skoY) 0)) (and (or (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1) (and (not (<= (* (- 1) skoX) 0)) (and (or (not (<= (* (- 1) skoX) 0)) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))))))
(set-info :status sat)
(check-sat)
