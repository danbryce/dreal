(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 120 skoY) (* (- 60) (* skoY pi)) (* (- 20) (* skoX skoX skoY)) (* 10 (* skoY skoY skoY pi)) (* skoX skoX skoX skoX skoY)) 0) (and (<= pi 0) (and (not (<= (+ (* 120 skoX) (* (- 60) (* skoX pi)) (* (- 20) (* skoX skoX skoX)) (* 10 (* skoX skoY skoY pi)) (* skoX skoX skoX skoX skoX)) 0)) (and (not (<= (+ (* 12 skoY) (* (- 6) (* skoY pi)) (* skoY skoY skoY pi)) 0)) (and (not (<= (+ (* (- 2000) skoY) (* 1000 pi)) 1)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= skoX 0)) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))))
(set-info :status unsat)
(check-sat)
