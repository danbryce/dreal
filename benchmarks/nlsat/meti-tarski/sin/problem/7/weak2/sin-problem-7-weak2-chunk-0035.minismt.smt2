(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* (- 2000) skoX) skoA) 0) (and (<= (+ (* 2000 skoX) (* (- 1) skoA)) 0) (and (not (<= (+ (* (- 1) skoX) skoA) 0)) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 2) skoA) pi) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963)))))))))
(set-info :status sat)
(check-sat)
