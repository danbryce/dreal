(set-logic QF_NRA)
(declare-fun c2 () Real)
(declare-fun x2 () Real)
(declare-fun om () Real)
(declare-fun d1 () Real)
(declare-fun c1 () Real)
(declare-fun x1 () Real)
(declare-fun d2 () Real)
(declare-fun y2 () Real)
(declare-fun e1 () Real)
(declare-fun y1 () Real)
(declare-fun e2 () Real)
(declare-fun e2uscore1dollarsk!1 () Real)
(declare-fun d2uscore1dollarsk!3 () Real)
(declare-fun e1uscore1dollarsk!0 () Real)
(declare-fun d1uscore1dollarsk!2 () Real)
(assert (= (+ d1 (* (- 1) (* c2 om)) (* x2 om)) 0))
(assert (= (+ d2 (* om c1) (* (- 1) (* om x1))) 0))
(assert (= (+ e1 (* (- 1) (* c2 om)) (* om y2)) 0))
(assert (= (+ e2 (* om c1) (* (- 1) (* om y1))) 0))
(assert (not (= (+ d1 (* (- 1) e1)) 0)))
(assert false)
(check-sat)
