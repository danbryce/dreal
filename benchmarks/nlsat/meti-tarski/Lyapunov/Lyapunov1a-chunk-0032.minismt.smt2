(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= skoZ 0)) (and (or (not (<= (+ (* 493 skoY) (* 2540 skoX) (* (- 17200) skoZ)) 0)) (not (<= (+ (* (- 493) skoY) (* (- 2540) skoX) (* 17200 skoZ)) 0))) (and (not (<= (+ (* 413 (* skoY skoZ)) (* 2130 (* skoX skoZ)) (* (- 7200) (* skoZ skoZ)) (* (- 26100) (* skoX skoX)) (* (- 14100) (* skoY skoY)) (* (- 10500) (* skoY skoX))) (- 1000))) (or (not (= skoX 0)) (or (not (= skoY 0)) (not (= skoZ 0))))))))
(set-info :status sat)
(check-sat)
