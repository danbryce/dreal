(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (<= (* (- 1) (* skoY skoX)) (- 1)) (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= (+ (* 2835 skoZ) (* (- 2835) (* skoY skoX skoZ)) (* 945 (* skoX skoX skoX)) (* 2835 (* skoY skoY skoX)) (* 2835 (* skoY skoX skoX)) (* 945 (* skoY skoY skoY)) (* 945 (* skoX skoX skoZ)) (* 3150 (* skoY skoY skoZ)) (* 1995 (* skoY skoY skoX skoX skoX)) (* 2205 (* skoY skoY skoY skoY skoX)) (* 3465 (* skoY skoY skoY skoX skoX)) (* (- 945) (* skoY skoX skoX skoX skoZ)) (* (- 3150) (* skoY skoY skoY skoX skoZ)) (* 1050 (* skoY skoY skoX skoX skoZ)) (* 675 (* skoY skoY skoY skoY skoZ)) (* 483 (* skoY skoY skoY skoY skoY)) (* 960 (* skoY skoY skoY skoY skoX skoX skoX)) (* (- 1050) (* skoY skoY skoY skoX skoX skoX skoZ)) (* (- 675) (* skoY skoY skoY skoY skoY skoX skoZ)) (* 225 (* skoY skoY skoY skoY skoX skoX skoZ)) (* 192 (* skoY skoY skoY skoY skoY skoY skoX)) (* 836 (* skoY skoY skoY skoY skoY skoX skoX)) (* (- 225) (* skoY skoY skoY skoY skoY skoX skoX skoX skoZ)) (* 64 (* skoY skoY skoY skoY skoY skoY skoX skoX skoX))) 0)) (and (or (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0) (<= (+ (* 3 skoZ) (* (- 3) (* skoY skoX skoZ)) (* skoX skoX skoX) (* 3 (* skoY skoY skoX)) (* 3 (* skoY skoX skoX)) (* skoX skoX skoZ) (* skoY skoY skoX skoX skoX) (* (- 1) (* skoY skoX skoX skoX skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))))))
(set-info :status unsat)
(check-sat)
