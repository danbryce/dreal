(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS2 () Real)
(declare-fun skoSM () Real)
(declare-fun skoSP () Real)
(assert (and (not (<= (* skoX (* skoX (- 1.))) 0.)) (and (not (<= skoX 0.)) (and (not (<= skoSP 0.)) (and (not (<= skoSM 0.)) (and (not (<= skoS2 0.)) (not (<= 1. skoX))))))))
(set-info :status unsat)
(check-sat)
