(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* (- 1) (* skoX skoX)) (- 2)) (and (<= (* skoX skoX) 2) (and (not (<= (+ (* (- 576) (* skoY skoX pi)) (* 192 (* skoY skoY skoY skoX pi)) (* (- 24) (* skoY skoY skoY skoY skoY skoX pi)) (* skoY skoY skoY skoY skoY skoY skoY skoX pi)) (- 288))) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))
(set-info :status unsat)
(check-sat)
