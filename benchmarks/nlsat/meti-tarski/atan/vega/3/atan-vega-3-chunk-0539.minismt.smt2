(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ (* 3 (* skoX skoX)) (* 4 (* skoX skoY)) (* 6 (* skoX skoZ)) (* 6 (* skoY skoZ)) (* 3 (* skoZ skoZ)) (* 3 (* skoY skoY)) (* skoX skoX skoY skoY) (* (- 6) (* skoX skoX skoY skoZ)) (* (- 6) (* skoX skoY skoY skoZ)) (* (- 6) (* skoX skoY skoZ skoZ)) (* 3 (* skoX skoX skoY skoY skoZ skoZ))) (- 1)) (and (or (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX) (* skoX skoX skoZ) (* (- 1) (* skoX skoX skoX skoY skoZ)) (* skoX skoX skoX skoY skoY)) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))))
(set-info :status unsat)
(check-sat)
