(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (* (- 1) skoX) 0) (or (<= (+ (* 3 skoZ) (* skoX skoX skoX) (* skoX skoX skoZ) (* (- 3) (* skoX skoY skoZ)) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* (- 1) (* skoX skoX skoX skoY skoZ)) (* skoX skoX skoX skoY skoY)) 0) (<= (+ (* 9 skoZ) (* (- 3) (* skoX skoX skoZ)) (* (- 30) (* skoX skoY skoZ)) (* (- 6) (* skoY skoY skoZ)) (* (- 3) (* skoX skoZ skoZ)) (* (- 3) (* skoY skoZ skoZ)) (* (- 3) (* skoY skoY skoY)) (* (- 2) (* skoX skoX skoX skoY skoZ)) (* (- 8) (* skoX skoX skoX skoY skoY)) (* (- 4) (* skoX skoX skoX skoX skoY)) (* (- 10) (* skoX skoX skoY skoY skoY)) (* 19 (* skoX skoX skoY skoY skoZ)) (* 6 (* skoX skoY skoY skoY skoZ)) (* 5 (* skoX skoX skoY skoZ skoZ)) (* 6 (* skoX skoY skoY skoZ skoZ)) (* (- 3) (* skoX skoX skoX skoX skoY skoY skoY)) (* 2 (* skoX skoX skoX skoY skoY skoY skoZ)) (* 5 (* skoX skoX skoX skoX skoY skoY skoZ)) (* (- 1) (* skoX skoX skoX skoY skoY skoZ skoZ)) (* (- 3) (* skoX skoX skoY skoY skoY skoZ skoZ)) (* (- 1) (* skoX skoX skoX skoX skoY skoY skoY skoZ skoZ))) 0)))) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* skoX skoX skoX) (* skoX skoX skoZ) (* (- 3) (* skoX skoY skoZ)) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* (- 1) (* skoX skoX skoX skoY skoZ)) (* skoX skoX skoX skoY skoY)) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status sat)
(check-sat)
