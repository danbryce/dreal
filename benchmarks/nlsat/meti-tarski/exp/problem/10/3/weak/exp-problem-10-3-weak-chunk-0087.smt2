(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoCM1 (+ 6. (* skoCM1 (- 12.)))) 1.)) (and (not (<= (* skoCM1 (+ (+ 12. (* skoC (* skoC 144.))) (* skoCM1 (* skoC (- 144.))))) (* skoC 12.))) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.)))))))
(set-info :status unsat)
(check-sat)
