(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* (- 1) (* skoX skoX)) (- 2)) (and (not (<= (+ (* (- 7257600) (* skoX skoX)) (* 2116800 (* skoX skoX skoX skoX)) (* (- 161280) (* skoX skoX skoX skoX skoX skoX)) (* 5220 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 92) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (<= (+ (* (- 5) pi) (* 10 skoY)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status unsat)
(check-sat)
