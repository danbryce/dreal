(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (not (<= (+ (* 29673 skoX) (* 29673 skoY) (* 29673 skoZ) (* (- 39900) (* skoX skoX)) (* (- 18900) (* skoX skoY)) (* (- 18900) (* skoX skoZ)) (* (- 18900) (* skoY skoZ)) (* (- 18900) (* skoY skoY)) (* 32970 (* skoX skoX skoX)) (* 32970 (* skoX skoX skoY)) (* 32970 (* skoX skoX skoZ)) (* (- 29673) (* skoX skoY skoZ)) (* (- 19200) (* skoX skoX skoX skoX)) (* (- 14700) (* skoX skoX skoX skoY)) (* (- 14700) (* skoX skoX skoX skoZ)) (* (- 2100) (* skoX skoX skoY skoZ)) (* 18900 (* skoX skoY skoY skoZ)) (* (- 21000) (* skoX skoX skoY skoY)) (* 7065 (* skoX skoX skoX skoX skoX)) (* 7065 (* skoX skoX skoX skoX skoY)) (* 7065 (* skoX skoX skoX skoX skoZ)) (* (- 32970) (* skoX skoX skoX skoY skoZ)) (* (- 1280) (* skoX skoX skoX skoX skoX skoX)) (* (- 1280) (* skoX skoX skoX skoX skoX skoY)) (* (- 1280) (* skoX skoX skoX skoX skoX skoZ)) (* 10200 (* skoX skoX skoX skoX skoY skoZ)) (* 21000 (* skoX skoX skoX skoY skoY skoZ)) (* (- 4500) (* skoX skoX skoX skoX skoY skoY)) (* (- 7065) (* skoX skoX skoX skoX skoX skoY skoZ)) (* 1280 (* skoX skoX skoX skoX skoX skoX skoY skoZ)) (* 4500 (* skoX skoX skoX skoX skoX skoY skoY skoZ))) 18900)) (and (or (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* skoX skoX skoX) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* skoX skoX skoZ) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX skoY skoY) (* (- 1) (* skoX skoX skoX skoY skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))))
(set-info :status sat)
(check-sat)
