(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 4) skoY) (* (- 4) (* skoY skoY skoX skoZ))) 0)) (and (or (not (<= (+ (* (- 11) (* skoY skoX)) (* 5 (* skoY skoY skoX)) (* 5 (* skoY skoX skoX)) (* 5 (* skoY skoY skoX skoX)) (* (- 15) (* skoY skoY skoX skoX skoZ)) (* skoY skoY skoX skoX skoX skoZ) (* skoY skoY skoY skoX skoX skoZ) (* skoY skoY skoY skoX skoX skoX skoZ)) 0)) (not (<= skoZ 1))) (and (or (not (<= skoY 1)) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (or (not (<= skoY 1)) (not (<= skoZ 1)))) (and (or (not (<= skoX 1)) (not (<= skoZ 1))) (and (or (not (<= (+ skoY skoX (* skoY skoX) (* (- 14) (* skoY skoX skoZ)) (* 2 (* skoY skoY skoX skoZ)) (* 2 (* skoY skoX skoX skoZ)) (* 2 (* skoY skoY skoX skoX skoZ))) (- 1))) (not (<= skoZ 1))) (and (or (not (<= skoX 1)) (not (<= skoY 1))) (or (not (<= (+ (* (- 11) (* skoY skoX)) (* 5 (* skoY skoX skoX)) (* 5 (* skoY skoX skoZ)) (* 5 (* skoY skoX skoX skoZ)) (* (- 15) (* skoY skoY skoX skoX skoZ)) (* skoY skoY skoX skoX skoX skoZ) (* skoY skoY skoX skoX skoZ skoZ) (* skoY skoY skoX skoX skoX skoZ skoZ)) 0)) (not (<= skoY 1)))))))))))
(set-info :status sat)
(check-sat)
