(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (or (not (<= (+ (* (- 176) skoY) (* (- 176) skoX) (* (- 176) skoZ) (* 71 (* skoX skoX)) (* (- 1522) (* skoY skoX)) (* 71 (* skoY skoY)) (* (- 1522) (* skoY skoZ)) (* (- 1522) (* skoX skoZ)) (* 71 (* skoZ skoZ)) (* 2 (* skoX skoX skoX)) (* (- 34) (* skoY skoX skoX)) (* (- 34) (* skoY skoY skoX)) (* 2 (* skoY skoY skoY)) (* (- 5740) (* skoY skoX skoZ)) (* (- 34) (* skoX skoX skoZ)) (* (- 34) (* skoY skoY skoZ)) (* (- 34) (* skoY skoZ skoZ)) (* (- 34) (* skoX skoZ skoZ)) (* 2 (* skoZ skoZ skoZ)) (* 4 (* skoY skoX skoX skoX)) (* 8 (* skoY skoY skoX skoX)) (* 4 (* skoY skoY skoY skoX)) (* (- 420) (* skoY skoX skoX skoZ)) (* (- 420) (* skoY skoY skoX skoZ)) (* (- 420) (* skoY skoX skoZ skoZ)) (* 4 (* skoX skoX skoX skoZ)) (* 4 (* skoY skoY skoY skoZ)) (* 8 (* skoX skoX skoZ skoZ)) (* 8 (* skoY skoY skoZ skoZ)) (* 4 (* skoY skoZ skoZ skoZ)) (* 4 (* skoX skoZ skoZ skoZ)) (* 8 (* skoY skoX skoX skoX skoZ)) (* 16 (* skoY skoY skoX skoX skoZ)) (* 8 (* skoY skoY skoY skoX skoZ)) (* 16 (* skoY skoX skoX skoZ skoZ)) (* 16 (* skoY skoY skoX skoZ skoZ)) (* 8 (* skoY skoX skoZ skoZ skoZ))) (- 160))) (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ)) (- 1)))) (and (not (<= (* 20 skoZ) 1)) (and (not (<= (* 20 skoY) 1)) (and (not (<= (* 20 skoX) 1)) (and (not (<= (* (- 1) skoZ) (- 15))) (and (not (<= (* (- 1) skoY) (- 15))) (not (<= (* (- 1) skoX) (- 15))))))))))
(set-info :status sat)
(check-sat)
