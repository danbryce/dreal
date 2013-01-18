(set-logic QF_NRA)
(declare-fun skoA () Real)
(declare-fun skoB () Real)
(declare-fun skoT () Real)
(assert (and (<= (+ skoA skoB) 0) (and (not (<= skoT 1)) (not (<= (+ (* (- 1) skoA) skoB) 0)))))
(set-info :status sat)
(check-sat)
