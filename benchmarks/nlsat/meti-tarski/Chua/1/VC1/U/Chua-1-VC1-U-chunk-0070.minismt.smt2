(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0) (and (not (<= skoX 0)) (and (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0) (and (or (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (not (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status sat)
(check-sat)
