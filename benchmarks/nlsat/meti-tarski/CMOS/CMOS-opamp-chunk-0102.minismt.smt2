(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 120000000000000000000 (* skoX skoX)) (* 3600119999 (* skoX skoX skoX skoX)) (* (- 3600060000000000000000000) (* skoX skoX skoY skoY)) (* (- 3600060000) (* skoX skoX skoX skoX skoY skoY)) (* 900000000000000000000000 (* skoX skoX skoY skoY skoY skoY)) (* 900000000 (* skoX skoX skoX skoX skoY skoY skoY skoY))) 970000000000000000000000000000) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= skoX 120) (<= (* (- 1) skoX) (- 100)))))))))
(set-info :status sat)
(check-sat)
