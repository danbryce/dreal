(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* (- 1) (* skoSQ3 skoSQ3 skoSQ3 skoSQ3)) 0)) (and (not (<= (+ (* 2160 (* skoSQ3 skoSQ3)) (* (- 720) (* skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 30 (* skoX skoX skoX skoX skoSQ3 skoSQ3)) (* (- 1) (* skoX skoX skoX skoX skoX skoX)) (* (- 30) (* skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3))) 0)) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)))))))))
(set-info :status unsat)
(check-sat)
