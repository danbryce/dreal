(set-logic QF_NRA)
(declare-fun yuscore2dollarsk!1 () Real)
(declare-fun stuscore2dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!2 () Real)
(assert (= yuscore2dollarsk!1 10))
(assert (= stuscore2dollarsk!0 0))
(assert (>= yuscore2dollarsk!1 1))
(assert (<= yuscore2dollarsk!1 12))
(assert (>= (+ yuscore2dollarsk!1 (* 2 xuscore2dollarsk!2)) 5))
(assert (not (= stuscore2dollarsk!0 1)))
(assert (not (<= yuscore2dollarsk!1 10)))
(check-sat)
