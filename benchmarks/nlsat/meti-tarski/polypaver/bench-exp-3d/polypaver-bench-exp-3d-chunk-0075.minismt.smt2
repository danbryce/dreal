(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 60) skoY) (* (- 60) skoX) (* (- 60) skoZ) (* 12 (* skoX skoX)) (* 12 (* skoY skoY)) (* 24 (* skoY skoX)) (* 24 (* skoY skoZ)) (* 24 (* skoX skoZ)) (* 12 (* skoZ skoZ)) (* (- 3) (* skoX skoX skoZ)) (* (- 3) (* skoY skoY skoZ)) (* (- 6) (* skoY skoX skoZ)) (* (- 3) (* skoY skoZ skoZ)) (* (- 3) (* skoX skoZ skoZ)) (* (- 1) (* skoZ skoZ skoZ)) (* (- 1) (* skoX skoX skoX)) (* (- 3) (* skoY skoX skoX)) (* (- 1) (* skoY skoY skoY)) (* (- 3) (* skoY skoY skoX))) (- 120))) (and (<= (* (- 1) skoX) 0) (and (<= (* (- 1) skoY) 0) (and (<= (* (- 1) skoZ) 0) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= (+ skoY skoX skoZ) 2) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ)) (- 2)))))))))))
(set-info :status sat)
(check-sat)
