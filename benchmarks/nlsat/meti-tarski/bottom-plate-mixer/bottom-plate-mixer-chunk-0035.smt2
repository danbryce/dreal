(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (/ 760000. 7383.) (* skoC (/ (- 3400.) 7383.))) skoS)) (and (<= skoX (/ 1. 10000000.)) (<= 0. skoX))))
(set-info :status sat)
(check-sat)
