(set-logic QF_NRA)
(declare-fun ruscore2dollarsk!1 () Real)
(declare-fun buscore2dollarsk!2 () Real)
(declare-fun auscore2dollarsk!0 () Real)
(assert (= (+ (* buscore2dollarsk!2 buscore2dollarsk!2 buscore2dollarsk!2) (* ruscore2dollarsk!1 ruscore2dollarsk!1 ruscore2dollarsk!1) (* 2 (* auscore2dollarsk!0 auscore2dollarsk!0 auscore2dollarsk!0)) (* 2 (* buscore2dollarsk!2 auscore2dollarsk!0 auscore2dollarsk!0)) (* 2 (* buscore2dollarsk!2 buscore2dollarsk!2 auscore2dollarsk!0)) (* (- 2) (* ruscore2dollarsk!1 buscore2dollarsk!2 auscore2dollarsk!0)) (* ruscore2dollarsk!1 buscore2dollarsk!2 buscore2dollarsk!2) (* (- 2) (* ruscore2dollarsk!1 ruscore2dollarsk!1 auscore2dollarsk!0)) (* (- 1) (* ruscore2dollarsk!1 ruscore2dollarsk!1 buscore2dollarsk!2))) 1))
(assert (not (= (+ (* buscore2dollarsk!2 buscore2dollarsk!2 buscore2dollarsk!2) (* ruscore2dollarsk!1 ruscore2dollarsk!1 ruscore2dollarsk!1) (* 2 (* auscore2dollarsk!0 auscore2dollarsk!0 auscore2dollarsk!0)) (* 2 (* buscore2dollarsk!2 auscore2dollarsk!0 auscore2dollarsk!0)) (* 2 (* buscore2dollarsk!2 buscore2dollarsk!2 auscore2dollarsk!0)) (* (- 2) (* ruscore2dollarsk!1 buscore2dollarsk!2 auscore2dollarsk!0)) (* ruscore2dollarsk!1 buscore2dollarsk!2 buscore2dollarsk!2) (* (- 2) (* ruscore2dollarsk!1 ruscore2dollarsk!1 auscore2dollarsk!0)) (* (- 1) (* ruscore2dollarsk!1 ruscore2dollarsk!1 buscore2dollarsk!2))) 1)))
(check-sat)
