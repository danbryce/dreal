(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoSP1 () Real)
(assert (and (= (+ 1. (* skoSM1 skoSM1)) skoX) (and (= (* skoS skoS) skoX) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX)))))))))
(set-info :status sat)
(check-sat)