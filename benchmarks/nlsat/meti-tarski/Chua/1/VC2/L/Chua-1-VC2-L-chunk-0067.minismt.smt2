(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 3) skoC) (* 13 skoS)) 0) (and (not (<= skoX 0)) (and (<= (+ (* (- 3) skoC) (* 13 skoS)) 0) (and (or (not (<= (+ (* 3 skoC) (* (- 13) skoS)) 0)) (not (<= (+ (* (- 3) skoC) (* 13 skoS)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status sat)
(check-sat)
