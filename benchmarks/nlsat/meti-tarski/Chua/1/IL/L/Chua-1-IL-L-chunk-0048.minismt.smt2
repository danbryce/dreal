(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 114000) skoX) (* (- 361) (* skoX skoX))) 12000000)) (and (not (<= (+ (* 235 skoC) (* 42 skoS)) 0)) (not (<= skoX 0)))))
(set-info :status unsat)
(check-sat)
