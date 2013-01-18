(set-logic QF_NRA)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (+ (* (- 1) skoX) skoA) 0)) (and (not (<= skoX 0)) (and (not (<= (+ pi (* (- 2) skoA)) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))
(set-info :status sat)
(check-sat)
