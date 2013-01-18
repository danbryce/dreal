(set-logic QF_NRA)
(declare-fun yuscore2dollarsk!1 () Real)
(declare-fun stuscore2dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!2 () Real)
(assert (= yuscore2dollarsk!1 10.0))
(assert (= stuscore2dollarsk!0 0.0))
(assert (>= yuscore2dollarsk!1 1.0))
(assert (<= yuscore2dollarsk!1 12.0))
(assert (>= yuscore2dollarsk!1 (+ 5.0 (* (- 2.0) xuscore2dollarsk!2))))
(assert (not (= stuscore2dollarsk!0 1.0)))
(assert (not (<= yuscore2dollarsk!1 10.0)))
(check-sat)
