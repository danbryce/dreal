(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoS (+ 1. (* skoB (/ (- 207.) 100.)))) (* skoB (+ skoA (* skoB (- 1.)))))) (and (not (<= skoB 1.)) (and (not (<= skoS 0.)) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status sat)
(check-sat)
