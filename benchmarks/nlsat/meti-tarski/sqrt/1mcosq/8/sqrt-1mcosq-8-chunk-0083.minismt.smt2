(set-logic QF_NRA)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* (- 2) (* pi skoX)) 0)) (and (not (<= (+ (* (- 1) skoX) skoY) 0)) (and (<= (* (- 10) skoX) (- 1)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (<= (+ (* (- 5) pi) (* 10 skoY)) (- 2))))))))
(set-info :status unsat)
(check-sat)