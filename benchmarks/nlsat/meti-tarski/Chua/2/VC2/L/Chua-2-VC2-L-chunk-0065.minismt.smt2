(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 76) skoC) (* 15 skoS)) 0) (and (<= skoX 0) (and (<= (+ (* (- 76) skoC) (* 15 skoS)) 0) (and (or (not (<= (+ (* 76 skoC) (* (- 15) skoS)) 0)) (not (<= (+ (* (- 76) skoC) (* 15 skoS)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))))
(set-info :status sat)
(check-sat)
