(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* (- 1) skoC) 0)) (and (not (<= (+ (* 12 skoC) (* (- 12) skoCM1) (* (- 144) (* skoC skoC skoCM1)) (* 144 (* skoC skoCM1 skoCM1))) 0)) (and (not (<= skoX 1)) (and (not (<= skoCM1 0)) (not (<= skoC 0)))))))
(set-info :status unsat)
(check-sat)
