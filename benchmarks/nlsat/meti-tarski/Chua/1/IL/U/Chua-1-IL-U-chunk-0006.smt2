(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= skoS (* skoC (/ (- 235.) 42.))) (and (<= skoX 289.) (<= 0. skoX))))
(set-info :status sat)
(check-sat)
