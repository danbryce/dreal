(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* 3 (* skoX skoX)) (* 4 (* skoSQ3 skoSQ3))) 18)) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1))))))))
(set-info :status sat)
(check-sat)
