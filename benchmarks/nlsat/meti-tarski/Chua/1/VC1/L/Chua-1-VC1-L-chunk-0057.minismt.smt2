(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ (* (- 1770) skoC) (* 689 skoS)) 0) (and (or (not (<= (+ (* 1770 skoC) (* (- 689) skoS)) 0)) (<= skoX 0)) (and (or (<= (+ (* (- 1770) skoC) (* 689 skoS)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status sat)
(check-sat)
