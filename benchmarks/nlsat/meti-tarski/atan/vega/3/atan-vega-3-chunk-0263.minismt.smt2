(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* (- 3) skoY) (* (- 3) skoX) (* (- 3) skoZ) (* (- 1) (* skoY skoY skoX)) (* 3 (* skoY skoX skoZ)) (* (- 1) (* skoY skoY skoZ)) (* (- 1) (* skoY skoY skoY)) (* skoY skoY skoY skoX skoZ)) 0) (and (<= (+ (* 3 skoY) (* 3 skoX) (* 3 skoZ) (* skoY skoY skoX) (* (- 3) (* skoY skoX skoZ)) (* skoY skoY skoZ) (* skoY skoY skoY) (* (- 1) (* skoY skoY skoY skoX skoZ))) 0) (and (<= (+ (* 471 skoY) (* 471 skoX) (* 471 skoZ) (* (- 400) (* skoY skoY)) (* (- 300) (* skoY skoZ)) (* 157 (* skoY skoY skoX)) (* (- 471) (* skoY skoX skoZ)) (* 157 (* skoY skoY skoZ)) (* 157 (* skoY skoY skoY)) (* 100 (* skoY skoY skoY skoX)) (* 300 (* skoY skoY skoX skoZ)) (* (- 157) (* skoY skoY skoY skoX skoZ))) 300) (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ skoY skoX skoZ (* (- 1) (* skoY skoX skoZ))) 0)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0) (<= (+ (* 3 skoZ) (* 3 (* skoY skoY skoX)) (* (- 3) (* skoY skoX skoZ)) (* skoX skoX skoX) (* skoX skoX skoZ) (* 3 (* skoY skoX skoX)) (* (- 1) (* skoY skoX skoX skoX skoZ)) (* skoY skoY skoX skoX skoX)) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))))
(set-info :status unsat)
(check-sat)
