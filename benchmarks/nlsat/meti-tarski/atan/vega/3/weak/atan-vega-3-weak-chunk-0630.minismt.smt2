(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* 315 (* skoX skoX)) (* 105 (* skoX skoX skoX skoX)) (* 5 (* skoX skoX skoX skoX skoX skoX))) (- 231))) (and (not (<= (+ (* (- 13860) skoZ) (* (- 4725) (* skoX skoX)) (* 3465 (* skoX skoY)) (* (- 1155) (* skoY skoY)) (* (- 4620) (* skoX skoX skoX)) (* (- 13860) (* skoX skoX skoY)) (* (- 13860) (* skoX skoY skoY)) (* (- 18900) (* skoX skoX skoZ)) (* 13860 (* skoX skoY skoZ)) (* (- 4620) (* skoY skoY skoZ)) (* (- 4620) (* skoY skoY skoY)) (* (- 1575) (* skoX skoX skoX skoX)) (* 4725 (* skoX skoX skoX skoY)) (* (- 1575) (* skoX skoX skoY skoY)) (* 1155 (* skoX skoY skoY skoY)) (* (- 3528) (* skoX skoX skoX skoX skoX)) (* (- 14280) (* skoX skoX skoX skoX skoY)) (* (- 20440) (* skoX skoX skoX skoY skoY)) (* (- 6300) (* skoX skoX skoX skoX skoZ)) (* 18900 (* skoX skoX skoX skoY skoZ)) (* (- 6300) (* skoX skoX skoY skoY skoZ)) (* 4620 (* skoX skoY skoY skoY skoZ)) (* (- 10920) (* skoX skoX skoY skoY skoY)) (* (- 75) (* skoX skoX skoX skoX skoX skoX)) (* 1575 (* skoX skoX skoX skoX skoX skoY)) (* (- 525) (* skoX skoX skoX skoX skoY skoY)) (* 1575 (* skoX skoX skoX skoY skoY skoY)) (* (- 300) (* skoX skoX skoX skoX skoX skoX skoX)) (* (- 2772) (* skoX skoX skoX skoX skoX skoX skoY)) (* (- 7476) (* skoX skoX skoX skoX skoX skoY skoY)) (* (- 300) (* skoX skoX skoX skoX skoX skoX skoZ)) (* 6300 (* skoX skoX skoX skoX skoX skoY skoZ)) (* (- 2100) (* skoX skoX skoX skoX skoY skoY skoZ)) (* 6300 (* skoX skoX skoX skoY skoY skoY skoZ)) (* (- 6860) (* skoX skoX skoX skoX skoY skoY skoY)) (* 75 (* skoX skoX skoX skoX skoX skoX skoX skoY)) (* (- 25) (* skoX skoX skoX skoX skoX skoX skoY skoY)) (* 525 (* skoX skoX skoX skoX skoX skoY skoY skoY)) (* (- 400) (* skoX skoX skoX skoX skoX skoX skoX skoY skoY)) (* 300 (* skoX skoX skoX skoX skoX skoX skoX skoY skoZ)) (* (- 100) (* skoX skoX skoX skoX skoX skoX skoY skoY skoZ)) (* 2100 (* skoX skoX skoX skoX skoX skoY skoY skoY skoZ)) (* (- 1024) (* skoX skoX skoX skoX skoX skoX skoY skoY skoY)) (* 25 (* skoX skoX skoX skoX skoX skoX skoX skoY skoY skoY)) (* 100 (* skoX skoX skoX skoX skoX skoX skoX skoY skoY skoY skoZ))) 3465)) (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (* (- 1) skoX) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))))
(set-info :status sat)
(check-sat)
