(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1) skoZ) (* (- 1) skoY) (* (- 1) skoX)) 0) (and (not (<= (+ (* (- 5040) skoZ) (* (- 5040) skoY) (* (- 5040) skoX) (* 840 (* skoX skoX skoX)) (* 2520 (* skoY skoX skoX)) (* 840 (* skoY skoY skoY)) (* 2520 (* skoY skoY skoX)) (* 2520 (* skoZ skoX skoX)) (* 2520 (* skoZ skoY skoY)) (* 5040 (* skoZ skoY skoX)) (* 840 (* skoZ skoZ skoZ)) (* 2520 (* skoZ skoZ skoY)) (* 2520 (* skoZ skoZ skoX)) (* (- 42) (* skoX skoX skoX skoX skoX)) (* (- 210) (* skoY skoX skoX skoX skoX)) (* (- 420) (* skoY skoY skoX skoX skoX)) (* (- 420) (* skoY skoY skoY skoX skoX)) (* (- 42) (* skoY skoY skoY skoY skoY)) (* (- 210) (* skoY skoY skoY skoY skoX)) (* (- 210) (* skoZ skoX skoX skoX skoX)) (* (- 840) (* skoZ skoY skoX skoX skoX)) (* (- 1260) (* skoZ skoY skoY skoX skoX)) (* (- 210) (* skoZ skoY skoY skoY skoY)) (* (- 840) (* skoZ skoY skoY skoY skoX)) (* (- 420) (* skoZ skoZ skoX skoX skoX)) (* (- 1260) (* skoZ skoZ skoY skoX skoX)) (* (- 420) (* skoZ skoZ skoY skoY skoY)) (* (- 1260) (* skoZ skoZ skoY skoY skoX)) (* (- 420) (* skoZ skoZ skoZ skoX skoX)) (* (- 420) (* skoZ skoZ skoZ skoY skoY)) (* (- 840) (* skoZ skoZ skoZ skoY skoX)) (* (- 42) (* skoZ skoZ skoZ skoZ skoZ)) (* (- 210) (* skoZ skoZ skoZ skoZ skoY)) (* (- 210) (* skoZ skoZ skoZ skoZ skoX)) (* 7 (* skoZ skoX skoX skoX skoX skoX skoX)) (* 42 (* skoZ skoY skoX skoX skoX skoX skoX)) (* 105 (* skoZ skoY skoY skoX skoX skoX skoX)) (* 140 (* skoZ skoY skoY skoY skoX skoX skoX)) (* 105 (* skoZ skoY skoY skoY skoY skoX skoX)) (* 7 (* skoZ skoY skoY skoY skoY skoY skoY)) (* 42 (* skoZ skoY skoY skoY skoY skoY skoX)) (* 21 (* skoZ skoZ skoX skoX skoX skoX skoX)) (* 105 (* skoZ skoZ skoY skoX skoX skoX skoX)) (* 210 (* skoZ skoZ skoY skoY skoX skoX skoX)) (* 210 (* skoZ skoZ skoY skoY skoY skoX skoX)) (* 21 (* skoZ skoZ skoY skoY skoY skoY skoY)) (* 105 (* skoZ skoZ skoY skoY skoY skoY skoX)) (* 35 (* skoZ skoZ skoZ skoX skoX skoX skoX)) (* 140 (* skoZ skoZ skoZ skoY skoX skoX skoX)) (* 210 (* skoZ skoZ skoZ skoY skoY skoX skoX)) (* 35 (* skoZ skoZ skoZ skoY skoY skoY skoY)) (* 140 (* skoZ skoZ skoZ skoY skoY skoY skoX)) (* 35 (* skoZ skoZ skoZ skoZ skoX skoX skoX)) (* 105 (* skoZ skoZ skoZ skoZ skoY skoX skoX)) (* 35 (* skoZ skoZ skoZ skoZ skoY skoY skoY)) (* 105 (* skoZ skoZ skoZ skoZ skoY skoY skoX)) (* 21 (* skoZ skoZ skoZ skoZ skoZ skoX skoX)) (* 21 (* skoZ skoZ skoZ skoZ skoZ skoY skoY)) (* 42 (* skoZ skoZ skoZ skoZ skoZ skoY skoX)) (* skoZ skoZ skoZ skoZ skoZ skoZ skoZ) (* 7 (* skoZ skoZ skoZ skoZ skoZ skoZ skoY)) (* 7 (* skoZ skoZ skoZ skoZ skoZ skoZ skoX)) (* skoX skoX skoX skoX skoX skoX skoX) (* 7 (* skoY skoX skoX skoX skoX skoX skoX)) (* 21 (* skoY skoY skoX skoX skoX skoX skoX)) (* 35 (* skoY skoY skoY skoX skoX skoX skoX)) (* 35 (* skoY skoY skoY skoY skoX skoX skoX)) (* 21 (* skoY skoY skoY skoY skoY skoX skoX)) (* skoY skoY skoY skoY skoY skoY skoY) (* 7 (* skoY skoY skoY skoY skoY skoY skoX))) 0)) (and (not (<= (* (- 1) skoX) (- 3))) (and (not (<= (* (- 1) skoY) (- 3))) (and (not (<= (* (- 1) skoZ) (- 3))) (and (not (<= (* 10 skoX) 1)) (and (not (<= (* 10 skoY) 1)) (not (<= (* 10 skoZ) 1))))))))))
(set-info :status sat)
(check-sat)
