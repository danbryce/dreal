(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= skoX 0) (and (not (<= (+ (* (- 42) skoS) (* (- 235) skoC)) 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))
(set-info :status sat)
(check-sat)
