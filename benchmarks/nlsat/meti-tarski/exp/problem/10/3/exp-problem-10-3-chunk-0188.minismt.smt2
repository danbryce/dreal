(set-logic QF_NRA)
(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 2) skoCP1) (* 24 (* skoCM1 skoCP1)) (* (- 120) (* skoCM1 skoCM1 skoCP1)) (* 240 (* skoCM1 skoCM1 skoCM1 skoCP1))) 0) (and (<= (+ (* 2 skoCP1) (* (- 24) (* skoCM1 skoCP1)) (* 120 (* skoCM1 skoCM1 skoCP1)) (* (- 240) (* skoCM1 skoCM1 skoCM1 skoCP1))) 0) (and (not (<= (+ (* (- 120) skoCM1) skoCP1 (* 600 (* skoCM1 skoCM1)) (* (- 252) (* skoCM1 skoCP1)) (* (- 1200) (* skoCM1 skoCM1 skoCM1)) (* 60 (* skoCM1 skoCM1 skoCP1)) (* (- 2520) (* skoCM1 skoCM1 skoCM1 skoCP1))) (- 10))) (and (= (+ (* (- 1) skoX) (* skoCP1 skoCP1 skoCP1)) 1) (and (= (+ (* (- 1) skoX) (* skoCM1 skoCM1 skoCM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoC skoC skoC)) 0) (and (not (<= skoX 2)) (and (not (<= skoCP1 0)) (and (not (<= skoCM1 0)) (and (not (<= skoC 0)) (not (<= (* (- 1) skoX) (- 10))))))))))))))
(set-info :status unsat)
(check-sat)
