(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ (* 3 skoZ) (* (- 1) (* skoX skoX skoX)) (* (- 2) (* skoX skoX skoZ)) (* (- 10) (* skoX skoY skoZ)) (* (- 2) (* skoY skoY skoZ)) (* (- 1) (* skoX skoZ skoZ)) (* (- 1) (* skoY skoZ skoZ)) (* (- 1) (* skoY skoY skoY)) (* (- 3) (* skoX skoX skoX skoY skoY)) (* (- 3) (* skoX skoX skoY skoY skoY)) (* 2 (* skoX skoX skoX skoY skoZ)) (* 7 (* skoX skoX skoY skoY skoZ)) (* 2 (* skoX skoY skoY skoY skoZ)) (* 2 (* skoX skoX skoY skoZ skoZ)) (* 2 (* skoX skoY skoY skoZ skoZ)) (* (- 1) (* skoX skoX skoX skoY skoY skoZ skoZ)) (* (- 1) (* skoX skoX skoY skoY skoY skoZ skoZ))) 0) (and (not (<= (+ (* skoX skoX) (* (- 4) (* skoX skoY)) (* skoY skoY) (* 2 (* skoX skoZ)) (* 2 (* skoY skoZ)) (* skoZ skoZ) (* 3 (* skoX skoX skoY skoY)) (* (- 2) (* skoX skoX skoY skoZ)) (* (- 2) (* skoX skoY skoY skoZ)) (* (- 2) (* skoX skoY skoZ skoZ)) (* skoX skoX skoY skoY skoZ skoZ)) (- 3))) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* skoX skoX skoX) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* skoX skoX skoZ) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX skoY skoY) (* (- 1) (* skoX skoX skoX skoY skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))))
(set-info :status sat)
(check-sat)
