(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 12 skoX) (* (- 6) (* pi skoX)) (* skoY skoY pi skoX)) 0) (and (not (<= (+ (* 12 skoY) (* (- 6) (* skoY pi)) (* skoY skoY skoY pi)) 0)) (and (not (<= (+ (* (- 2000) skoY) (* 1000 pi)) 1)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= skoX 0)) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
