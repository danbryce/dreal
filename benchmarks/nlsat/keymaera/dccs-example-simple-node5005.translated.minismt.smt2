(set-logic QF_NRA)
(declare-fun t2uscore0dollarsk!0 () Real)
(declare-fun eps () Real)
(declare-fun v1uscore2dollarsk!3 () Real)
(declare-fun v2 () Real)
(declare-fun x1uscore2dollarsk!2 () Real)
(declare-fun x2uscore2dollarsk!1 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun v1 () Real)
(declare-fun B () Real)
(declare-fun A () Real)
(assert (or (not (>= t2uscore0dollarsk!0 0)) (and (>= v1uscore2dollarsk!3 0) (>= (+ (* (- 1) t2uscore0dollarsk!0) eps) 0))))
(assert (>= t2uscore0dollarsk!0 0))
(assert (= v1uscore2dollarsk!3 0))
(assert (<= (+ v1uscore2dollarsk!3 (* (- 1) v2)) 0))
(assert (not (<= (+ (* (- 1) x1uscore2dollarsk!2) x2uscore2dollarsk!1) 0)))
(assert (>= v1uscore2dollarsk!3 0))
(assert (not (<= (+ (* (- 1) x1) x2) 0)))
(assert (>= v1 0))
(assert (>= v2 0))
(assert (<= (+ (* (- 1) v2) v1) 0))
(assert (not (<= B 0)))
(assert (not (<= eps 0)))
(assert (not (<= A 0)))
(assert (not (<= (+ v1uscore2dollarsk!3 (* (- 1) v2) (* eps A)) 0)))
(assert (<= (+ (* (- 1) x1uscore2dollarsk!2) x2uscore2dollarsk!1 (* t2uscore0dollarsk!0 v2) (* (- 1) (* t2uscore0dollarsk!0 v1uscore2dollarsk!3))) 0))
(assert (or (and (<= eps 0) (not (= eps 0))) (>= (+ (* (- 1) t2uscore0dollarsk!0) eps) 0)))
(assert (or (not (>= t2uscore0dollarsk!0 0)) (and (>= v1uscore2dollarsk!3 0) (>= eps 0))))
(check-sat)
