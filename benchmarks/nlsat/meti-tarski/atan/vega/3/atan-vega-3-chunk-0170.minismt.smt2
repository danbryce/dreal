(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (<= (+ skoX skoY skoZ (* (- 1) (* skoX skoY skoZ))) 0) (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (* skoX skoX) (- 3))) (and (not (<= (+ (* 471 skoX) (* 471 skoY) (* 471 skoZ) (* (- 400) (* skoX skoX)) (* (- 300) (* skoX skoY)) (* (- 300) (* skoX skoZ)) (* (- 300) (* skoY skoZ)) (* (- 300) (* skoY skoY)) (* (- 471) (* skoX skoY skoZ)) (* 157 (* skoX skoX skoX)) (* 157 (* skoX skoX skoY)) (* 157 (* skoX skoX skoZ)) (* 200 (* skoX skoX skoY skoZ)) (* 300 (* skoX skoY skoY skoZ)) (* (- 100) (* skoX skoX skoY skoY)) (* (- 157) (* skoX skoX skoX skoY skoZ)) (* 100 (* skoX skoX skoX skoY skoY skoZ))) 300)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* skoX skoX skoZ) (* skoX skoX skoX skoY skoY) (* (- 1) (* skoX skoX skoX skoY skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))))))
(set-info :status unsat)
(check-sat)
