(set-logic QF_NRA)
(declare-fun N () Real)
(declare-fun nuscore2dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!1 () Real)
(declare-fun yuscore2dollarsk!2 () Real)
(declare-fun zuscore2dollarsk!3 () Real)
(assert (<= (+ (* (- 1) N) nuscore2dollarsk!0) 0))
(assert (= (+ (* (- 1) xuscore2dollarsk!1) (* nuscore2dollarsk!0 nuscore2dollarsk!0 nuscore2dollarsk!0)) 0))
(assert (= (+ (* 3 nuscore2dollarsk!0) (* (- 1) yuscore2dollarsk!2) (* 3 (* nuscore2dollarsk!0 nuscore2dollarsk!0))) (- 1)))
(assert (= (+ (* 6 nuscore2dollarsk!0) (* (- 1) zuscore2dollarsk!3)) (- 6)))
(assert (not (= (+ (* 9 nuscore2dollarsk!0) (* (- 1) yuscore2dollarsk!2) (* (- 1) zuscore2dollarsk!3) (* 3 (* nuscore2dollarsk!0 nuscore2dollarsk!0))) (- 7))))
(check-sat)
