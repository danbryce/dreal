(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ (* 2835 skoZ) (* 945 (* skoX skoX skoX)) (* 2835 (* skoY skoX skoX)) (* 2835 (* skoY skoY skoX)) (* 945 (* skoY skoY skoY)) (* 945 (* skoX skoX skoZ)) (* (- 2835) (* skoY skoX skoZ)) (* 3150 (* skoY skoY skoZ)) (* 1995 (* skoY skoY skoX skoX skoX)) (* 3465 (* skoY skoY skoY skoX skoX)) (* 2205 (* skoY skoY skoY skoY skoX)) (* (- 945) (* skoY skoX skoX skoX skoZ)) (* 1050 (* skoY skoY skoX skoX skoZ)) (* (- 3150) (* skoY skoY skoY skoX skoZ)) (* 675 (* skoY skoY skoY skoY skoZ)) (* 483 (* skoY skoY skoY skoY skoY)) (* 960 (* skoY skoY skoY skoY skoX skoX skoX)) (* (- 1050) (* skoY skoY skoY skoX skoX skoX skoZ)) (* 225 (* skoY skoY skoY skoY skoX skoX skoZ)) (* (- 675) (* skoY skoY skoY skoY skoY skoX skoZ)) (* 836 (* skoY skoY skoY skoY skoY skoX skoX)) (* 192 (* skoY skoY skoY skoY skoY skoY skoX)) (* (- 225) (* skoY skoY skoY skoY skoY skoX skoX skoX skoZ)) (* 64 (* skoY skoY skoY skoY skoY skoY skoX skoX skoX))) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status sat)
(check-sat)
