(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoCP1 () Real)
(assert (and (not (<= (* skoCM1 (+ 6. (* skoCM1 (- 12.)))) 1.)) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX))))))))
(set-info :status unsat)
(check-sat)
