(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 441) skoS) (* 400 skoC)) 0) (and (not (<= (+ (* 441 skoS) (* (- 400) skoC)) 0)) (and (or (not (<= (+ (* (- 441) skoS) (* 400 skoC)) 0)) (not (<= (+ (* 441 skoS) (* (- 400) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (or (not (<= (* (- 1) skoX) 0)) (or (not (<= (* 21 skoX) 1570)) (<= (* (- 1) skoS) 0))) (and (or (not (<= (* (- 1) skoX) 0)) (or (not (<= (* 21 skoX) 1570)) (<= (* (- 1) skoC) 0))) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))))
(set-info :status sat)
(check-sat)
