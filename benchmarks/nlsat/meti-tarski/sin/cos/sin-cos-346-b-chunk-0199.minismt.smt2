(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoSQ3 skoSQ3) 0) (and (<= (+ (* 72 (* skoSQ3 skoSQ3)) (* 36 (* skoX skoX)) (* (- 12) (* skoX skoX skoSQ3 skoSQ3)) (* skoX skoX skoX skoX skoSQ3 skoSQ3)) 216) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)) (= (* skoSQ3 skoSQ3) 3)))))))))
(set-info :status unsat)
(check-sat)
