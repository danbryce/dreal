(set-logic QF_NRA)
(declare-fun skoSM1 () Real)
(declare-fun skoS () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 24 skoSM1) (* (- 120) (* skoSM1 skoSM1)) (* 240 (* skoSM1 skoSM1 skoSM1))) 2) (and (not (<= (+ (* (- 12) skoSM1) (* 60 (* skoSM1 skoSM1)) (* (- 120) (* skoSM1 skoSM1 skoSM1))) (- 1))) (and (= (+ (* (- 1) skoX) (* skoSP1 skoSP1)) 1) (and (= (+ (* (- 1) skoX) (* skoSM1 skoSM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoS skoS)) 0) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5)))))))))))))
(set-info :status sat)
(check-sat)
