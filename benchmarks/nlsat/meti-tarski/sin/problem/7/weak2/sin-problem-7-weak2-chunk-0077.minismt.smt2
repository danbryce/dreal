(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(declare-fun pi () Real)
(assert (and (not (<= skoA 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ (* (- 2) skoA) pi) 0)) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 1) skoX) skoA) 0)) (and (or (not (<= (+ (* (- 2000) skoX) skoA) 0)) (not (<= (+ (* 2000 skoX) (* (- 1) skoA)) 0))) (and (or (not (<= (+ (* (- 3) (* skoA skoA)) (* 1000 (* skoX skoX skoX skoA))) 0)) (<= (+ (* 2000 skoX) (* (- 1) skoA)) 0)) (<= (+ (* (- 2000) skoX) skoA) 0))))))))))
(set-info :status sat)
(check-sat)
