(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoX () Real)
(declare-fun skoCM1 () Real)
(assert (and (not (= (* skoC (* skoC skoC)) skoX)) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.))))))
(set-info :status sat)
(check-sat)
