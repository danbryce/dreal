(set-logic QF_NRA)
(declare-fun y0 () Real)
(declare-fun cuscore0dollarsk!1 () Real)
(declare-fun buscore0dollarsk!2 () Real)
(declare-fun x0 () Real)
(declare-fun xuscore0dollarsk!0 () Real)
(assert (not (<= y0 0)))
(assert (not (<= cuscore0dollarsk!1 0)))
(assert (= (+ (* cuscore0dollarsk!1 cuscore0dollarsk!1) (* (- 1) (* buscore0dollarsk!2 buscore0dollarsk!2))) 1))
(assert (= (+ (* cuscore0dollarsk!1 cuscore0dollarsk!1) (* (- 1) (* buscore0dollarsk!2 buscore0dollarsk!2)) (* (- 1) (* x0 x0)) (* (- 1) (* y0 y0)) (* 2 (* y0 buscore0dollarsk!2))) 0))
(assert (= (+ (* y0 xuscore0dollarsk!0) (* cuscore0dollarsk!1 xuscore0dollarsk!0) (* (- 1) (* buscore0dollarsk!2 xuscore0dollarsk!0)) (* (- 1) (* cuscore0dollarsk!1 x0)) (* buscore0dollarsk!2 x0)) 0))
(assert (not (= x0 0)))
(assert (<= (+ (* 2 (* x0 xuscore0dollarsk!0)) (* (- 1) (* xuscore0dollarsk!0 xuscore0dollarsk!0))) 0))
(check-sat)
