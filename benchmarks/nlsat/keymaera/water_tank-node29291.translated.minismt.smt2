(set-logic QF_NRA)
(declare-fun xuscore2dollarsk!3 () Real)
(declare-fun t21uscore0dollarsk!0 () Real)
(declare-fun stuscore2dollarsk!1 () Real)
(declare-fun yuscore2dollarsk!2 () Real)
(assert (or (not (>= t21uscore0dollarsk!0 0)) (<= (+ xuscore2dollarsk!3 t21uscore0dollarsk!0) 2)))
(assert (>= t21uscore0dollarsk!0 0))
(assert (not (<= xuscore2dollarsk!3 2)))
(assert (= stuscore2dollarsk!1 3))
(assert (>= yuscore2dollarsk!2 1))
(assert (<= yuscore2dollarsk!2 12))
(assert (>= (+ (* 2 xuscore2dollarsk!3) yuscore2dollarsk!2) 5))
(assert (not (= stuscore2dollarsk!1 1)))
(assert (not (>= (+ (* (- 2) t21uscore0dollarsk!0) yuscore2dollarsk!2) 1)))
(assert (or (and (>= xuscore2dollarsk!3 2) (not (= xuscore2dollarsk!3 2))) (<= (+ xuscore2dollarsk!3 t21uscore0dollarsk!0) 2)))
(assert (or (not (>= t21uscore0dollarsk!0 0)) (<= xuscore2dollarsk!3 2)))
(check-sat)
