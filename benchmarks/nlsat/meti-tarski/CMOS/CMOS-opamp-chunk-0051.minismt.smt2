(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* 3600000000 (* skoX skoX)) (- 3600000000000000000000000))) (and (not (<= (+ (* 3600120000 (* skoX skoX)) (* (- 1800000000000000000000000) (* skoY skoY)) (* (- 1800000000) (* skoY skoY skoX skoX)) (* 150000000000000000000000 (* skoY skoY skoY skoY)) (* 150000000 (* skoY skoY skoY skoY skoX skoX))) (- 3600120000000000000000000))) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= skoX 120) (<= (* (- 1) skoX) (- 100))))))))))
(set-info :status sat)
(check-sat)
