(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* (- 2) skoS) (- 1))) (and (not (<= (+ (* 2 skoS) (* (- 3) skoSP1) (* (- 2) (* skoS skoSP1))) 1)) (and (not (<= (+ (* (- 2) skoS) (* 3 skoSM1) (* 2 (* skoS skoSM1))) (- 1))) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5)))))))))))
(set-info :status unsat)
(check-sat)
