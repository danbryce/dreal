(set-logic QF_NRA)
(declare-fun skoSM1 () Real)
(declare-fun skoS () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(assert (and (<= skoSM1 0) (and (= (+ (* (- 1) skoX) (* skoSP1 skoSP1)) 1) (and (= (+ (* (- 1) skoX) (* skoSM1 skoSM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoS skoS)) 0) (and (<= (* (- 1) skoSP1) 0) (and (<= (* (- 1) skoSM1) 0) (and (<= (* (- 1) skoS) 0) (not (<= (* 5 skoX) 7))))))))))
(set-info :status unsat)
(check-sat)
