(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (= (+ (* (- 7) (* skoX skoY)) (* 21 (* skoX skoX skoY skoY)) (* (- 35) (* skoX skoX skoX skoY skoY skoY)) (* 35 (* skoX skoX skoX skoX skoY skoY skoY skoY)) (* (- 21) (* skoX skoX skoX skoX skoX skoY skoY skoY skoY skoY)) (* 7 (* skoX skoX skoX skoX skoX skoX skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoX skoX skoX skoX skoX skoX skoX skoY skoY skoY skoY skoY skoY skoY))) (- 1)) (and (not (= (* (- 1) (* skoX skoY)) (- 1))) (and (not (= (+ (* (- 6) (* skoX skoY)) (* 15 (* skoX skoX skoY skoY)) (* (- 20) (* skoX skoX skoX skoY skoY skoY)) (* 15 (* skoX skoX skoX skoX skoY skoY skoY skoY)) (* (- 6) (* skoX skoX skoX skoX skoX skoY skoY skoY skoY skoY)) (* skoX skoX skoX skoX skoX skoX skoY skoY skoY skoY skoY skoY)) (- 1))) (and (not (= (+ (* (- 5) (* skoX skoY)) (* 10 (* skoX skoX skoY skoY)) (* (- 10) (* skoX skoX skoX skoY skoY skoY)) (* 5 (* skoX skoX skoX skoX skoY skoY skoY skoY)) (* (- 1) (* skoX skoX skoX skoX skoX skoY skoY skoY skoY skoY))) (- 1))) (and (not (= (+ (* (- 4) (* skoX skoY)) (* 6 (* skoX skoX skoY skoY)) (* (- 4) (* skoX skoX skoX skoY skoY skoY)) (* skoX skoX skoX skoX skoY skoY skoY skoY)) (- 1))) (and (not (= (+ (* (- 3) (* skoX skoY)) (* 3 (* skoX skoX skoY skoY)) (* (- 1) (* skoX skoX skoX skoY skoY skoY))) (- 1))) (and (not (= (+ (* (- 2) (* skoX skoY)) (* skoX skoX skoY skoY)) (- 1))) (and (not (<= (* (- 1) skoY) 0)) (and (or (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1) (and (not (<= (* (- 1) skoX) 0)) (and (or (not (<= (* (- 1) skoX) 0)) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))))))))))))))
(set-info :status unsat)
(check-sat)
