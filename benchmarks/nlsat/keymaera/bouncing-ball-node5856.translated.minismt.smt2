(set-logic QF_NRA)
(declare-fun g () Real)
(declare-fun huscore2dollarsk!2 () Real)
(declare-fun vuscore2dollarsk!3 () Real)
(declare-fun t1uscore0dollarsk!0 () Real)
(declare-fun tuscore2dollarsk!1 () Real)
(declare-fun V () Real)
(declare-fun c () Real)
(declare-fun v () Real)
(declare-fun t () Real)
(declare-fun h () Real)
(assert (or (= g 0) (and (not (= g 0)) (not (= vuscore2dollarsk!3 0)) (or (>= vuscore2dollarsk!3 0) (>= g 0)) (or (<= vuscore2dollarsk!3 0) (<= g 0))) (and (not (= g 0)) (not (= (+ vuscore2dollarsk!3 (* (- 1) (* g t1uscore0dollarsk!0))) 0)) (or (>= (+ vuscore2dollarsk!3 (* (- 1) (* g t1uscore0dollarsk!0))) 0) (<= g 0)) (or (<= (+ vuscore2dollarsk!3 (* (- 1) (* g t1uscore0dollarsk!0))) 0) (>= g 0))) (= g 0) (= (+ (* 2 (* g huscore2dollarsk!2)) (* vuscore2dollarsk!3 vuscore2dollarsk!3)) 0) (and (not (<= (+ (* 2 (* g huscore2dollarsk!2)) (* vuscore2dollarsk!3 vuscore2dollarsk!3)) 0)) (not (<= g 0))) (and (not (>= (+ (* 2 (* g huscore2dollarsk!2)) (* vuscore2dollarsk!3 vuscore2dollarsk!3)) 0)) (not (>= g 0)))))
(assert (>= t1uscore0dollarsk!0 0))
(assert (= (+ (* 2 huscore2dollarsk!2) (* (- 2) (* vuscore2dollarsk!3 tuscore2dollarsk!1)) (* (- 1) (* g tuscore2dollarsk!1 tuscore2dollarsk!1))) 0))
(assert (>= huscore2dollarsk!2 0))
(assert (>= tuscore2dollarsk!1 0))
(assert (<= (+ vuscore2dollarsk!3 (* (- 1) V) (* g tuscore2dollarsk!1)) 0))
(assert (not (<= g 0)))
(assert (<= (* (- 1) c) 0))
(assert (not (<= (* (- 1) c) (- 1))))
(assert (= (+ (* 2 h) (* (- 2) (* v t)) (* (- 1) (* g t t))) 0))
(assert (>= h 0))
(assert (>= t 0))
(assert (<= (+ (* (- 1) V) v (* g t)) 0))
(assert (<= (+ t1uscore0dollarsk!0 tuscore2dollarsk!1) 0))
(assert (not (<= (+ vuscore2dollarsk!3 (* (- 1) V) (* g tuscore2dollarsk!1)) 0)))
(assert (or (not (>= t1uscore0dollarsk!0 0)) (>= (+ (* 2 huscore2dollarsk!2) (* 2 (* vuscore2dollarsk!3 t1uscore0dollarsk!0)) (* (- 1) (* g t1uscore0dollarsk!0 t1uscore0dollarsk!0))) 0)))
(assert (or (not (>= t1uscore0dollarsk!0 0)) (>= huscore2dollarsk!2 0)))
(check-sat)
