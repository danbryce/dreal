(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* (- 6000) skoX) (* (- 1000000) (* skoX skoX))) 12) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= (* 5 skoX) 4) (<= (* (- 500) skoX) (- 1))))))
(set-info :status sat)
(check-sat)
