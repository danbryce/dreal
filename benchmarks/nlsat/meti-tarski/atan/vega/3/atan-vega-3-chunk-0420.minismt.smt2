(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (<= (+ (* (- 3) (* skoX skoX)) (* (- 4) (* skoY skoX)) (* (- 6) (* skoY skoZ)) (* (- 6) (* skoX skoZ)) (* (- 3) (* skoZ skoZ)) (* (- 3) (* skoY skoY)) (* (- 1) (* skoY skoY skoX skoX)) (* 6 (* skoY skoX skoX skoZ)) (* 6 (* skoY skoY skoX skoZ)) (* 6 (* skoY skoX skoZ skoZ)) (* (- 3) (* skoY skoY skoX skoX skoZ skoZ))) 1) (and (<= (+ (* 3 (* skoX skoX)) (* 4 (* skoY skoX)) (* 6 (* skoY skoZ)) (* 6 (* skoX skoZ)) (* 3 (* skoZ skoZ)) (* 3 (* skoY skoY)) (* skoY skoY skoX skoX) (* (- 6) (* skoY skoX skoX skoZ)) (* (- 6) (* skoY skoY skoX skoZ)) (* (- 6) (* skoY skoX skoZ skoZ)) (* 3 (* skoY skoY skoX skoX skoZ skoZ))) (- 1)) (and (<= (+ (* (- 200) skoY) (* (- 150) skoX) (* (- 150) skoZ) (* (- 237) (* skoX skoX)) (* (- 316) (* skoY skoX)) (* (- 474) (* skoY skoZ)) (* (- 474) (* skoX skoZ)) (* (- 237) (* skoZ skoZ)) (* (- 237) (* skoY skoY)) (* (- 50) (* skoY skoY skoX)) (* (- 150) (* skoY skoZ skoZ)) (* (- 300) (* skoY skoY skoZ)) (* (- 150) (* skoY skoY skoY)) (* (- 79) (* skoY skoY skoX skoX)) (* 474 (* skoY skoX skoX skoZ)) (* 474 (* skoY skoY skoX skoZ)) (* 474 (* skoY skoX skoZ skoZ)) (* 150 (* skoY skoY skoX skoX skoZ)) (* (- 50) (* skoY skoY skoY skoX skoX)) (* 300 (* skoY skoY skoX skoZ skoZ)) (* 300 (* skoY skoY skoY skoX skoZ)) (* (- 237) (* skoY skoY skoX skoX skoZ skoZ)) (* (- 150) (* skoY skoY skoY skoX skoX skoZ skoZ))) 79) (and (or (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0) (<= (+ (* 3 skoZ) (* 3 (* skoY skoX skoX)) (* 3 (* skoY skoY skoX)) (* (- 3) (* skoY skoX skoZ)) (* skoX skoX skoX) (* skoX skoX skoZ) (* (- 1) (* skoY skoX skoX skoX skoZ)) (* skoY skoY skoX skoX skoX)) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))))
(set-info :status unsat)
(check-sat)
