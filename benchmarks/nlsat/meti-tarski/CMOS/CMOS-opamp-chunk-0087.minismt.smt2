(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* 120000000000000000000 (* skoX skoX)) (* 3600119999 (* skoX skoX skoX skoX)) (* (- 3600060000000000000000000) (* skoY skoY skoX skoX)) (* (- 3600060000) (* skoY skoY skoX skoX skoX skoX)) (* 1050005000000000000000000 (* skoY skoY skoY skoY skoX skoX)) (* 1050005000 (* skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 75000000000000000000000) (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 75000000) (* skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX))) 970000000000000000000000000000)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))
(set-info :status sat)
(check-sat)
