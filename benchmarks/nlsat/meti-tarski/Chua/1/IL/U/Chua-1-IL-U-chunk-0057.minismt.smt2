(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= skoX 0) (and (not (<= (* 19 skoX) 1000)) (and (<= (+ (* 235 skoC) (* 42 skoS)) 0) (and (or (not (<= (+ (* (- 235) skoC) (* (- 42) skoS)) 0)) (not (<= (+ (* 235 skoC) (* 42 skoS)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status unsat)
(check-sat)
