(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* (- 1800060000) (* skoX skoX)) (* 900000000000000000000000 (* skoY skoY)) (* 900000000 (* skoY skoY skoX skoX)) (* (- 75000000000000000000000) (* skoY skoY skoY skoY)) (* (- 75000000) (* skoY skoY skoY skoY skoX skoX))) 1800060000000000000000000) (and (<= (* (- 1) skoX) (- 100)) (and (<= skoX 120) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))))
(set-info :status sat)
(check-sat)
