(set-logic QF_NRA)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(assert (and (not (= (* skoSP1 skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1 skoSP1) 0)) (and (not (= (* skoSP1 skoSP1) 0)) (and (not (= skoSP1 0)) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5))))))))))))
(set-info :status sat)
(check-sat)
