(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* (- 6) skoY) (* (- 6) skoX) (* (- 6) skoZ) (* (- 3) (* skoX skoX)) (* (- 130) (* skoY skoX)) (* (- 3) (* skoY skoY)) (* (- 130) (* skoY skoZ)) (* (- 130) (* skoX skoZ)) (* (- 3) (* skoZ skoZ)) (* 4 (* skoX skoX skoX)) (* (- 88) (* skoY skoX skoX)) (* (- 88) (* skoY skoY skoX)) (* 4 (* skoY skoY skoY)) (* (- 668) (* skoY skoX skoZ)) (* (- 88) (* skoX skoX skoZ)) (* (- 88) (* skoY skoY skoZ)) (* (- 88) (* skoY skoZ skoZ)) (* (- 88) (* skoX skoZ skoZ)) (* 4 (* skoZ skoZ skoZ)) (* 8 (* skoY skoX skoX skoX)) (* 16 (* skoY skoY skoX skoX)) (* 8 (* skoY skoY skoY skoX)) (* (- 340) (* skoY skoX skoX skoZ)) (* (- 340) (* skoY skoY skoX skoZ)) (* (- 340) (* skoY skoX skoZ skoZ)) (* 8 (* skoX skoX skoX skoZ)) (* 8 (* skoY skoY skoY skoZ)) (* 16 (* skoX skoX skoZ skoZ)) (* 16 (* skoY skoY skoZ skoZ)) (* 8 (* skoY skoZ skoZ skoZ)) (* 8 (* skoX skoZ skoZ skoZ)) (* 16 (* skoY skoX skoX skoX skoZ)) (* 32 (* skoY skoY skoX skoX skoZ)) (* 16 (* skoY skoY skoY skoX skoZ)) (* 32 (* skoY skoX skoX skoZ skoZ)) (* 32 (* skoY skoY skoX skoZ skoZ)) (* 16 (* skoY skoX skoZ skoZ skoZ))) (- 5))) (and (not (<= (* 20 skoZ) 1)) (and (not (<= (* 20 skoY) 1)) (and (not (<= (* 20 skoX) 1)) (and (not (<= (* (- 1) skoZ) (- 15))) (and (not (<= (* (- 1) skoY) (- 15))) (not (<= (* (- 1) skoX) (- 15))))))))))
(set-info :status sat)
(check-sat)
