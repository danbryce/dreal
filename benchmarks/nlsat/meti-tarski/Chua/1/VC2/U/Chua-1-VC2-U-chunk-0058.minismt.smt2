(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (+ (* (- 13) skoS) (* 3 skoC)) 0)) (and (or (not (<= (+ (* 13 skoS) (* (- 3) skoC)) 0)) (<= skoX 0)) (and (or (<= (+ (* (- 13) skoS) (* 3 skoC)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status unsat)
(check-sat)
