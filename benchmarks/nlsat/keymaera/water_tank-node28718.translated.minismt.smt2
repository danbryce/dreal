(set-logic QF_NRA)
(declare-fun yuscore2dollarsk!1 () Real)
(declare-fun stuscore2dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!2 () Real)
(assert (= yuscore2dollarsk!1 5))
(assert (= stuscore2dollarsk!0 2))
(assert (>= yuscore2dollarsk!1 1))
(assert (<= yuscore2dollarsk!1 12))
(assert (<= (+ yuscore2dollarsk!1 (* (- 1) xuscore2dollarsk!2)) 10))
(assert (not (= stuscore2dollarsk!0 3)))
(assert (not (>= yuscore2dollarsk!1 5)))
(check-sat)
