(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoSP1 () Real)
(assert (and (not (= (+ (* (- 1) skoX) (* skoSM1 skoSM1)) (- 1))) (and (= (+ (* (- 1) skoX) (* skoS skoS)) 0) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5))))))))))
(set-info :status sat)
(check-sat)
