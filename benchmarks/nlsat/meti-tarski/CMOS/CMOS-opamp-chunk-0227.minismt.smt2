(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* 1800000000000000000000000 (* skoX skoX)) (* 1800000000 (* skoX skoX skoX skoX))) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* (- 1) pi) (* 3 skoY)) 0) (and (<= (+ pi (* (- 4) skoY)) 0) (and (<= skoX 120) (<= (* (- 1) skoX) (- 100)))))))))
(set-info :status sat)
(check-sat)
