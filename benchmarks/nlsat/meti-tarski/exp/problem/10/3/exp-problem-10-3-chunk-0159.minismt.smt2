(set-logic QF_NRA)
(declare-fun skoCP1 () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 2) (* skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1)) (* 12 (* skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCM1)) (* (- 24) (* skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCP1 skoCM1 skoCM1))) 0) (and (= (+ (* (- 1) skoX) (* skoCP1 skoCP1 skoCP1)) 1) (and (= (+ (* (- 1) skoX) (* skoCM1 skoCM1 skoCM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoC skoC skoC)) 0) (and (not (<= skoX 2)) (and (not (<= skoCP1 0)) (and (not (<= skoCM1 0)) (and (not (<= skoC 0)) (not (<= (* (- 1) skoX) (- 10))))))))))))
(set-info :status sat)
(check-sat)
