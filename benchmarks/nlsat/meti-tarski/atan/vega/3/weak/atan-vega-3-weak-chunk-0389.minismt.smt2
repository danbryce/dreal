(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* 1200 skoY) (* 900 skoX) (* 900 skoZ) (* 1197 (* skoX skoX)) (* 1596 (* skoY skoX)) (* 1330 (* skoY skoY)) (* 2394 (* skoY skoZ)) (* 2394 (* skoX skoZ)) (* 1197 (* skoZ skoZ)) (* 600 (* skoY skoY skoX)) (* 1200 (* skoY skoY skoY)) (* 2100 (* skoY skoY skoZ)) (* 900 (* skoY skoZ skoZ)) (* 798 (* skoY skoY skoX skoX)) (* 532 (* skoY skoY skoY skoX)) (* (- 1596) (* skoY skoY skoX skoZ)) (* (- 2394) (* skoY skoX skoX skoZ)) (* 798 (* skoY skoY skoY skoZ)) (* (- 2394) (* skoY skoX skoZ skoZ)) (* 399 (* skoY skoY skoZ skoZ)) (* 399 (* skoY skoY skoY skoY)) (* (- 300) (* skoY skoY skoY skoY skoX)) (* (- 900) (* skoY skoY skoX skoX skoZ)) (* (- 2400) (* skoY skoY skoY skoX skoZ)) (* (- 1800) (* skoY skoY skoX skoZ skoZ)) (* 133 (* skoY skoY skoY skoY skoX skoX)) (* (- 798) (* skoY skoY skoY skoX skoX skoZ)) (* (- 798) (* skoY skoY skoY skoY skoX skoZ)) (* 1197 (* skoY skoY skoX skoX skoZ skoZ)) (* (- 798) (* skoY skoY skoY skoX skoZ skoZ)) (* 300 (* skoY skoY skoY skoY skoX skoX skoZ)) (* 900 (* skoY skoY skoY skoX skoX skoZ skoZ)) (* 399 (* skoY skoY skoY skoY skoX skoX skoZ skoZ))) (- 399))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status sat)
(check-sat)
