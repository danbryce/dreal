(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* 3600000000 (* skoX skoX)) (- 3600000000000000000000000))) (and (not (<= (+ (* 7484649480000 (* skoX skoX)) (* (- 3742200000000000000000000000) (* skoY skoY)) (* (- 3742200000000) (* skoY skoY skoX skoX)) (* 311850000000000000000000000 (* skoY skoY skoY skoY)) (* 311850000000 (* skoY skoY skoY skoY skoX skoX)) (* (- 10395000000000000000000000) (* skoY skoY skoY skoY skoY skoY)) (* (- 10395000000) (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* 185625000000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 185625000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 2062500000000000000000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 2062500) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 15625000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 15625 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX))) (- 7484649480000000000000000000))) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (* (- 10000000) pi) (- 31415927)))))))
(set-info :status sat)
(check-sat)
