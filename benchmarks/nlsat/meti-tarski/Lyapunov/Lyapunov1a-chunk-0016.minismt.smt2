(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* 17200 skoZ) (* (- 493) skoY) (* (- 2540) skoX) (* (- 65500) (* skoZ skoZ)) (* 443 (* skoZ skoY)) (* 2290 (* skoZ skoX)) (* (- 50000) (* skoX skoX)) (* (- 50000) (* skoY skoY))) 0)) (and (not (<= (+ (* 17200 skoZ) (* (- 493) skoY) (* (- 2540) skoX)) 0)) (and (or (not (<= (+ (* (- 17200) skoZ) (* 493 skoY) (* 2540 skoX)) 0)) (not (<= (+ (* 17200 skoZ) (* (- 493) skoY) (* (- 2540) skoX)) 0))) (and (not (<= (+ (* (- 7200) (* skoZ skoZ)) (* 413 (* skoZ skoY)) (* 2130 (* skoZ skoX)) (* (- 26100) (* skoX skoX)) (* (- 14100) (* skoY skoY)) (* (- 10500) (* skoY skoX))) (- 1000))) (or (not (= skoX 0)) (or (not (= skoY 0)) (not (= skoZ 0)))))))))
(set-info :status sat)
(check-sat)
