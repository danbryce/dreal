(set-logic QF_NRA)
(declare-fun skoSP1 () Real)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoX () Real)
(assert (and (= (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1) 0) (and (not (= (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1) 0)) (and (not (= skoSP1 0)) (and (= (+ (* (- 1) skoX) (* skoSP1 skoSP1)) 1) (and (= (+ (* (- 1) skoX) (* skoSM1 skoSM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoS skoS)) 0) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5)))))))))))))))))))
(set-info :status unsat)
(check-sat)
