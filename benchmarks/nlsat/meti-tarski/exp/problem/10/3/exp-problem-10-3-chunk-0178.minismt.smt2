(set-logic QF_NRA)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoCP1 () Real)
(assert (and (not (<= (+ (* 24 skoCM1) (* (- 120) (* skoCM1 skoCM1)) (* 240 (* skoCM1 skoCM1 skoCM1))) 2)) (and (not (<= skoX 2)) (and (not (<= skoCP1 0)) (and (not (<= skoCM1 0)) (and (not (<= skoC 0)) (not (<= (* (- 1) skoX) (- 10)))))))))
(set-info :status sat)
(check-sat)
