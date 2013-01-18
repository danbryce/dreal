(set-logic QF_NRA)
(declare-fun t1uscore0dollarsk!0 () Real)
(declare-fun c () Real)
(declare-fun xuscore2dollarsk!1 () Real)
(declare-fun x () Real)
(assert (or (not (>= t1uscore0dollarsk!0 0.0))
            (>= (+ c (* (- 1.0) t1uscore0dollarsk!0)) 0.0)))
(assert (>= t1uscore0dollarsk!0 0.0))
(assert (not (<= xuscore2dollarsk!1 0.0)))
(assert (<= (* xuscore2dollarsk!1 xuscore2dollarsk!1) (* 16.0 c c)))
(assert (not (<= (* 16.0 c c) (* x x))))
(assert (not (<= (* (+ (* (- 4.0) t1uscore0dollarsk!0) xuscore2dollarsk!1)
                    (+ (* (- 4.0) t1uscore0dollarsk!0) xuscore2dollarsk!1))
                 (* 16.0 c c))))
(assert (or (and (<= c 0.0) (not (= c 0.0)))
            (>= (+ c (* (- 1.0) t1uscore0dollarsk!0)) 0.0)))
(assert (or (not (>= t1uscore0dollarsk!0 0.0)) (>= c 0.0)))
(check-sat)
