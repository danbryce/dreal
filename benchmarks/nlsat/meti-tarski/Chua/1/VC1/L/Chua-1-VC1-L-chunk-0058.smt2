(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= 0. skoX)) (not (<= skoS (* skoC (/ 1770. 689.))))))
(set-info :status sat)
(check-sat)
