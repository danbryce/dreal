(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= skoS (* skoC (/ 86400000. 2025130727.))) (and (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status sat)
(check-sat)
