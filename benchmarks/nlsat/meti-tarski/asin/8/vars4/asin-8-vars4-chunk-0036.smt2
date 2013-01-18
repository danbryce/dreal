(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(declare-fun skoS2 () Real)
(assert (and (not (<= (* skoX (+ (+ 4. skoSM) skoSP)) 0.)) (and (not (<= skoX 0.)) (and (not (<= skoSP 0.)) (and (not (<= skoSM 0.)) (and (not (<= skoS2 0.)) (not (<= 1. skoX))))))))
(set-info :status sat)
(check-sat)
