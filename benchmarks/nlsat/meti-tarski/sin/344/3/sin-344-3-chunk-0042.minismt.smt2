(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 5040) skoY) (* (- 5040) skoX) (* (- 5040) skoZ) (* 840 (* skoX skoX skoX)) (* 2520 (* skoY skoX skoX)) (* 840 (* skoY skoY skoY)) (* 2520 (* skoY skoY skoX)) (* 2520 (* skoX skoX skoZ)) (* 2520 (* skoY skoY skoZ)) (* 5040 (* skoY skoX skoZ)) (* 2520 (* skoY skoZ skoZ)) (* 2520 (* skoX skoZ skoZ)) (* 840 (* skoZ skoZ skoZ)) (* (- 42) (* skoX skoX skoX skoX skoX)) (* (- 210) (* skoY skoX skoX skoX skoX)) (* (- 420) (* skoY skoY skoX skoX skoX)) (* (- 420) (* skoY skoY skoY skoX skoX)) (* (- 42) (* skoY skoY skoY skoY skoY)) (* (- 210) (* skoY skoY skoY skoY skoX)) (* (- 210) (* skoX skoX skoX skoX skoZ)) (* (- 840) (* skoY skoX skoX skoX skoZ)) (* (- 1260) (* skoY skoY skoX skoX skoZ)) (* (- 210) (* skoY skoY skoY skoY skoZ)) (* (- 840) (* skoY skoY skoY skoX skoZ)) (* (- 420) (* skoX skoX skoX skoZ skoZ)) (* (- 1260) (* skoY skoX skoX skoZ skoZ)) (* (- 420) (* skoY skoY skoY skoZ skoZ)) (* (- 1260) (* skoY skoY skoX skoZ skoZ)) (* (- 420) (* skoX skoX skoZ skoZ skoZ)) (* (- 420) (* skoY skoY skoZ skoZ skoZ)) (* (- 840) (* skoY skoX skoZ skoZ skoZ)) (* (- 210) (* skoY skoZ skoZ skoZ skoZ)) (* (- 210) (* skoX skoZ skoZ skoZ skoZ)) (* (- 42) (* skoZ skoZ skoZ skoZ skoZ)) (* 7 (* skoX skoX skoX skoX skoX skoX skoZ)) (* 42 (* skoY skoX skoX skoX skoX skoX skoZ)) (* 105 (* skoY skoY skoX skoX skoX skoX skoZ)) (* 140 (* skoY skoY skoY skoX skoX skoX skoZ)) (* 105 (* skoY skoY skoY skoY skoX skoX skoZ)) (* 7 (* skoY skoY skoY skoY skoY skoY skoZ)) (* 42 (* skoY skoY skoY skoY skoY skoX skoZ)) (* 21 (* skoX skoX skoX skoX skoX skoZ skoZ)) (* 105 (* skoY skoX skoX skoX skoX skoZ skoZ)) (* 210 (* skoY skoY skoX skoX skoX skoZ skoZ)) (* 210 (* skoY skoY skoY skoX skoX skoZ skoZ)) (* 21 (* skoY skoY skoY skoY skoY skoZ skoZ)) (* 105 (* skoY skoY skoY skoY skoX skoZ skoZ)) (* 35 (* skoX skoX skoX skoX skoZ skoZ skoZ)) (* 140 (* skoY skoX skoX skoX skoZ skoZ skoZ)) (* 210 (* skoY skoY skoX skoX skoZ skoZ skoZ)) (* 35 (* skoY skoY skoY skoY skoZ skoZ skoZ)) (* 140 (* skoY skoY skoY skoX skoZ skoZ skoZ)) (* 35 (* skoX skoX skoX skoZ skoZ skoZ skoZ)) (* 105 (* skoY skoX skoX skoZ skoZ skoZ skoZ)) (* 35 (* skoY skoY skoY skoZ skoZ skoZ skoZ)) (* 105 (* skoY skoY skoX skoZ skoZ skoZ skoZ)) (* 21 (* skoX skoX skoZ skoZ skoZ skoZ skoZ)) (* 21 (* skoY skoY skoZ skoZ skoZ skoZ skoZ)) (* 42 (* skoY skoX skoZ skoZ skoZ skoZ skoZ)) (* 7 (* skoY skoZ skoZ skoZ skoZ skoZ skoZ)) (* 7 (* skoX skoZ skoZ skoZ skoZ skoZ skoZ)) (* skoZ skoZ skoZ skoZ skoZ skoZ skoZ) (* skoX skoX skoX skoX skoX skoX skoX) (* 7 (* skoY skoX skoX skoX skoX skoX skoX)) (* 21 (* skoY skoY skoX skoX skoX skoX skoX)) (* 35 (* skoY skoY skoY skoX skoX skoX skoX)) (* 35 (* skoY skoY skoY skoY skoX skoX skoX)) (* 21 (* skoY skoY skoY skoY skoY skoX skoX)) (* skoY skoY skoY skoY skoY skoY skoY) (* 7 (* skoY skoY skoY skoY skoY skoY skoX))) 0)) (and (not (<= (* (- 1) skoX) (- 3))) (and (not (<= (* (- 1) skoY) (- 3))) (and (not (<= (* (- 1) skoZ) (- 3))) (and (not (<= (* 10 skoX) 1)) (and (not (<= (* 10 skoY) 1)) (not (<= (* 10 skoZ) 1)))))))))
(set-info :status sat)
(check-sat)
