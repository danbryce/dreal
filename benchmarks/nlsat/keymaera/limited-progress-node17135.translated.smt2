(set-logic QF_NRA)
(declare-fun b () Real)
(declare-fun d2uscore2dollarsk!1 () Real)
(declare-fun d1uscore2dollarsk!0 () Real)
(declare-fun d2 () Real)
(declare-fun d1 () Real)
(assert (<= (+ (* d1uscore2dollarsk!0 d1uscore2dollarsk!0)
               (* d2uscore2dollarsk!1 d2uscore2dollarsk!1))
            (* b b)))
(assert (>= b 0.0))
(assert (<= (+ (* d1 d1) (* d2 d2)) (* b b)))
(assert (not (<= (* (- 1.0) b) d2uscore2dollarsk!1)))
(check-sat)
