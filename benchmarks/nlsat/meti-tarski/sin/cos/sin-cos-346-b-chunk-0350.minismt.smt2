(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* 3 (* skoSQ3 skoSQ3)) 0)) (and (not (<= (+ (* 120960 (* skoSQ3 skoSQ3)) (* (- 40320) (* skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 60480) (* skoX skoX skoSQ3 skoSQ3)) (* 3360 (* skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 20160 (* skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 56 (* skoX skoX skoX skoX skoX skoX)) (* (- 168) (* skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 3 (* skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3))) 0)) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)))))))))
(set-info :status sat)
(check-sat)
