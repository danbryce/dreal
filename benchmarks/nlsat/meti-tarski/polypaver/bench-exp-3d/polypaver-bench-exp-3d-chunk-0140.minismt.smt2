(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 540) skoY) (* (- 540) skoZ) (* (- 540) skoX) (* (- 84) (* skoX skoX)) (* (- 84) (* skoY skoY)) (* (- 168) (* skoY skoX)) (* (- 168) (* skoY skoZ)) (* (- 84) (* skoZ skoZ)) (* (- 168) (* skoZ skoX)) (* (- 27) (* skoZ skoX skoX)) (* (- 27) (* skoY skoY skoZ)) (* (- 54) (* skoY skoZ skoX)) (* (- 27) (* skoY skoZ skoZ)) (* (- 9) (* skoZ skoZ skoZ)) (* (- 27) (* skoZ skoZ skoX)) (* (- 9) (* skoX skoX skoX)) (* (- 27) (* skoY skoX skoX)) (* (- 9) (* skoY skoY skoY)) (* (- 27) (* skoY skoY skoX))) 840)) (not (<= (+ (* (- 60) skoY) (* (- 60) skoZ) (* 60 skoX) (* (- 12) (* skoX skoX)) (* 48 (* skoY skoY)) (* 36 (* skoY skoX)) (* (- 24) (* skoY skoZ)) (* 48 (* skoZ skoZ)) (* 36 (* skoZ skoX)) (* (- 9) (* skoZ skoX skoX)) (* 27 (* skoY skoY skoZ)) (* 18 (* skoY skoZ skoX)) (* 27 (* skoY skoZ skoZ)) (* (- 11) (* skoZ skoZ skoZ)) (* (- 21) (* skoZ skoZ skoX)) (* skoX skoX skoX) (* (- 9) (* skoY skoX skoX)) (* (- 11) (* skoY skoY skoY)) (* (- 21) (* skoY skoY skoX)) (* skoY skoX skoX skoX) (* 3 (* skoY skoY skoX skoX)) (* skoY skoY skoY skoY) (* 3 (* skoY skoY skoY skoX)) (* (- 18) (* skoY skoY skoZ skoZ)) (* (- 15) (* skoY skoZ skoZ skoX)) (* (- 8) (* skoY skoZ skoZ skoZ)) (* (- 6) (* skoY skoZ skoX skoX)) (* (- 8) (* skoY skoY skoY skoZ)) (* (- 15) (* skoY skoY skoZ skoX)) (* 3 (* skoZ skoZ skoX skoX)) (* skoZ skoZ skoZ skoZ) (* 3 (* skoZ skoZ skoZ skoX)) (* skoZ skoX skoX skoX) (* skoY skoZ skoX skoX skoX) (* 3 (* skoY skoY skoZ skoX skoX)) (* skoY skoY skoY skoY skoZ) (* 3 (* skoY skoY skoY skoZ skoX)) (* 3 (* skoY skoY skoZ skoZ skoZ)) (* 3 (* skoY skoZ skoZ skoZ skoX)) (* skoY skoZ skoZ skoZ skoZ) (* 3 (* skoY skoZ skoZ skoX skoX)) (* 3 (* skoY skoY skoY skoZ skoZ)) (* 6 (* skoY skoY skoZ skoZ skoX))) 120))))
(set-info :status sat)
(check-sat)
