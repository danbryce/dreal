(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 15) skoS) (* 76 skoC)) 0) (and (<= (+ (* 15 skoS) (* (- 76) skoC)) 0) (and (or (not (<= (+ (* (- 15) skoS) (* 76 skoC)) 0)) (not (<= (+ (* 15 skoS) (* (- 76) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))
(set-info :status unsat)
(check-sat)
