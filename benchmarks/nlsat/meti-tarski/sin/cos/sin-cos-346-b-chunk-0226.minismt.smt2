(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* (- 1) (* skoSQ3 skoSQ3)) 0)) (and (not (<= (+ (* (- 60480) (* skoX skoX)) (* 20160 (* skoX skoX skoSQ3 skoSQ3)) (* (- 1680) (* skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 56 (* skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3)) (* (- 1) (* skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3))) 0)) (and (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= skoX 0)) (not (<= skoSQ3 0)))))))))
(set-info :status unsat)
(check-sat)
