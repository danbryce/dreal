(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (not (<= (+ (* 29673 skoY) (* 29673 skoX) (* 29673 skoZ) (* (- 18900) (* skoY skoX)) (* (- 18900) (* skoX skoX)) (* (- 39900) (* skoY skoY)) (* (- 18900) (* skoY skoZ)) (* (- 18900) (* skoX skoZ)) (* (- 29673) (* skoY skoX skoZ)) (* 32970 (* skoY skoY skoX)) (* 32970 (* skoY skoY skoY)) (* 32970 (* skoY skoY skoZ)) (* (- 14700) (* skoY skoY skoY skoX)) (* (- 21000) (* skoY skoY skoX skoX)) (* (- 19200) (* skoY skoY skoY skoY)) (* (- 2100) (* skoY skoY skoX skoZ)) (* 18900 (* skoY skoX skoX skoZ)) (* (- 14700) (* skoY skoY skoY skoZ)) (* 7065 (* skoY skoY skoY skoY skoX)) (* 7065 (* skoY skoY skoY skoY skoY)) (* (- 32970) (* skoY skoY skoY skoX skoZ)) (* 7065 (* skoY skoY skoY skoY skoZ)) (* (- 1280) (* skoY skoY skoY skoY skoY skoX)) (* (- 4500) (* skoY skoY skoY skoY skoX skoX)) (* 10200 (* skoY skoY skoY skoY skoX skoZ)) (* 21000 (* skoY skoY skoY skoX skoX skoZ)) (* (- 1280) (* skoY skoY skoY skoY skoY skoZ)) (* (- 1280) (* skoY skoY skoY skoY skoY skoY)) (* (- 7065) (* skoY skoY skoY skoY skoY skoX skoZ)) (* 1280 (* skoY skoY skoY skoY skoY skoY skoX skoZ)) (* 4500 (* skoY skoY skoY skoY skoY skoX skoX skoZ))) 18900)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))
(set-info :status sat)
(check-sat)
