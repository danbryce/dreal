(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 4) skoY) (* (- 4) skoZ) skoX (* 2 (* skoY skoY)) (* 2 (* skoY skoX)) (* (- 24) (* skoY skoZ)) (* 2 (* skoZ skoZ)) (* 2 (* skoZ skoX)) (* 4 (* skoY skoY skoZ)) (* 4 (* skoY skoZ skoX)) (* 4 (* skoY skoZ skoZ))) (- 2))) (and (not (<= (* 20 skoZ) 1)) (and (not (<= (* 20 skoY) 1)) (and (not (<= (* 20 skoX) 1)) (and (not (<= (* (- 1) skoZ) (- 15))) (and (not (<= (* (- 1) skoY) (- 15))) (not (<= (* (- 1) skoX) (- 15))))))))))
(set-info :status sat)
(check-sat)
