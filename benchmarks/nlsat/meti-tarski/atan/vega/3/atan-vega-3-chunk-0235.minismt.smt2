(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (or (<= (* (- 1) skoY) 0) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 9 skoZ) (* (- 9) (* skoX skoY skoZ)) (* 3 (* skoX skoX skoX)) (* 9 (* skoX skoX skoY)) (* 9 (* skoX skoY skoY)) (* 3 (* skoX skoX skoZ)) (* 3 (* skoY skoY skoZ)) (* 3 (* skoY skoY skoY)) (* 4 (* skoX skoX skoX skoY skoY)) (* (- 3) (* skoX skoX skoX skoY skoZ)) (* skoX skoX skoY skoY skoZ) (* (- 3) (* skoX skoY skoY skoY skoZ)) (* 4 (* skoX skoX skoY skoY skoY)) (* (- 1) (* skoX skoX skoX skoY skoY skoY skoZ))) 0))) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* skoX skoX skoZ) (* skoX skoX skoX skoY skoY) (* (- 1) (* skoX skoX skoX skoY skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))
(set-info :status sat)
(check-sat)
