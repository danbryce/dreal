(set-logic QF_NRA)
(declare-fun stuscore2dollarsk!1 () Real)
(declare-fun yuscore2dollarsk!2 () Real)
(declare-fun t15uscore0dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!3 () Real)
(assert (= stuscore2dollarsk!1 3))
(assert (or (not (>= t15uscore0dollarsk!0 0)) (<= yuscore2dollarsk!2 10)))
(assert (>= t15uscore0dollarsk!0 0))
(assert (not (<= (* (- 1) yuscore2dollarsk!2) (- 10))))
(assert (= stuscore2dollarsk!1 0))
(assert (>= yuscore2dollarsk!2 1))
(assert (<= yuscore2dollarsk!2 12))
(assert (>= (+ yuscore2dollarsk!2 (* 2 xuscore2dollarsk!3)) 5))
(assert (not (= stuscore2dollarsk!1 1)))
(assert (not (>= (+ yuscore2dollarsk!2 (* 3 t15uscore0dollarsk!0) (* 2 xuscore2dollarsk!3)) 5)))
(assert (or (and (>= yuscore2dollarsk!2 10) (not (= yuscore2dollarsk!2 10))) (<= (+ yuscore2dollarsk!2 t15uscore0dollarsk!0) 10)))
(assert (or (not (>= t15uscore0dollarsk!0 0)) (<= (+ yuscore2dollarsk!2 t15uscore0dollarsk!0) 10)))
(check-sat)
