(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 1800000000000000000000000 (* skoX skoX)) (* 1800000000 (* skoX skoX skoX skoX)) (* (- 900000000000000000000000) (* skoX skoX skoY skoY)) (* (- 900000000) (* skoX skoX skoX skoX skoY skoY))) 0) (and (<= (+ (* (- 205193160000000000000000000) (* skoX skoX)) (* 6839943 (* skoX skoX skoX skoX)) (* (- 3420000000000000000000) (* skoX skoX skoY skoY)) (* (- 3420000) (* skoX skoX skoX skoX skoY skoY))) 55289999999999882000000000000057) (and (<= (+ (* (- 1800000000000000000000000) (* skoX skoX)) (* (- 1800000000) (* skoX skoX skoX skoX)) (* 900000000000000000000000 (* skoX skoX skoY skoY)) (* 900000000 (* skoX skoX skoX skoX skoY skoY))) 0) (and (<= (* (- 1) skoX) (- 100)) (and (<= skoX 120) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))))))
(set-info :status unsat)
(check-sat)
