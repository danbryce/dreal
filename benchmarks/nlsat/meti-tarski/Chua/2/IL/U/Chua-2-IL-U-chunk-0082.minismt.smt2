(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* 277 skoX) 30000)) (and (not (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))
(set-info :status unsat)
(check-sat)
