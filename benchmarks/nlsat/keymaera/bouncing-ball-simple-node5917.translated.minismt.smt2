(set-logic QF_NRA)
(declare-fun vuscore2dollarsk!3 () Real)
(declare-fun huscore2dollarsk!2 () Real)
(declare-fun t1uscore0dollarsk!0 () Real)
(declare-fun tuscore2dollarsk!1 () Real)
(declare-fun h () Real)
(declare-fun v () Real)
(assert (or (and (not (= vuscore2dollarsk!3 0)) (<= vuscore2dollarsk!3 0)) (not (>= (+ (* (- 10) vuscore2dollarsk!3) (* 100 t1uscore0dollarsk!0)) 0)) (>= (+ (* 100 huscore2dollarsk!2) (* 5 (* vuscore2dollarsk!3 vuscore2dollarsk!3))) 0)))
(assert (>= t1uscore0dollarsk!0 0))
(assert (= (+ huscore2dollarsk!2 (* (- 5) (* tuscore2dollarsk!1 tuscore2dollarsk!1)) (* (- 1) (* vuscore2dollarsk!3 tuscore2dollarsk!1))) 0))
(assert (>= huscore2dollarsk!2 0))
(assert (>= tuscore2dollarsk!1 0))
(assert (<= (+ vuscore2dollarsk!3 (* 10 tuscore2dollarsk!1)) 16))
(assert (<= (* 5 tuscore2dollarsk!1) 16))
(assert (= h 0))
(assert (= v 16))
(assert (<= (+ t1uscore0dollarsk!0 tuscore2dollarsk!1) 0))
(assert (not (= (+ huscore2dollarsk!2 (* (- 5) (* tuscore2dollarsk!1 tuscore2dollarsk!1)) (* (- 1) (* vuscore2dollarsk!3 tuscore2dollarsk!1))) 0)))
(assert (or (not (>= t1uscore0dollarsk!0 0)) (>= (+ huscore2dollarsk!2 (* (- 5) (* t1uscore0dollarsk!0 t1uscore0dollarsk!0)) (* vuscore2dollarsk!3 t1uscore0dollarsk!0)) 0)))
(assert (or (not (>= t1uscore0dollarsk!0 0)) (>= huscore2dollarsk!2 0)))
(check-sat)
