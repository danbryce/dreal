(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* (- 1) (* skoX skoX)) (- 2))) (and (not (<= (+ (* 144 (* skoX skoX)) (* (- 576) (* skoY skoX pi)) (* (- 36) (* skoX skoX skoX skoX)) (* 192 (* skoY skoY skoY skoX pi)) (* (- 24) (* skoY skoY skoY skoY skoY skoX pi)) (* skoY skoY skoY skoY skoY skoY skoY skoX pi)) (- 144))) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))
(set-info :status sat)
(check-sat)
