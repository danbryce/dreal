(set-logic QF_NRA)
(declare-fun stuscore2dollarsk!1 () Real)
(declare-fun xuscore2dollarsk!3 () Real)
(declare-fun t35uscore0dollarsk!0 () Real)
(declare-fun yuscore2dollarsk!2 () Real)
(assert (= stuscore2dollarsk!1 3))
(assert (or (not (>= t35uscore0dollarsk!0 0)) (<= xuscore2dollarsk!3 2)))
(assert (>= t35uscore0dollarsk!0 0))
(assert (not (<= (* (- 1) xuscore2dollarsk!3) (- 2))))
(assert (= stuscore2dollarsk!1 1))
(assert (>= yuscore2dollarsk!2 1))
(assert (<= yuscore2dollarsk!2 12))
(assert (>= (+ (* 2 xuscore2dollarsk!3) yuscore2dollarsk!2) 5))
(assert (<= (+ (* (- 1) xuscore2dollarsk!3) yuscore2dollarsk!2) 10))
(assert (not (>= (+ (* 2 xuscore2dollarsk!3) (* 3 t35uscore0dollarsk!0) yuscore2dollarsk!2) 5)))
(assert (or (and (>= xuscore2dollarsk!3 2) (not (= xuscore2dollarsk!3 2))) (<= (+ xuscore2dollarsk!3 t35uscore0dollarsk!0) 2)))
(assert (or (not (>= t35uscore0dollarsk!0 0)) (<= (+ xuscore2dollarsk!3 t35uscore0dollarsk!0) 2)))
(check-sat)
