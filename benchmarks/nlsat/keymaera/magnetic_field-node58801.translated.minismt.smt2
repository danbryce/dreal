(set-logic QF_NRA)
(declare-fun xuscore6dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun vyuscore6dollarsk!3 () Real)
(declare-fun vxuscore6dollarsk!2 () Real)
(declare-fun buscore2dollarsk!5 () Real)
(declare-fun yuscore6dollarsk!0 () Real)
(declare-fun stateuscore2dollarsk!4 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(declare-fun xuscore2dollarsk!6 () Real)
(declare-fun vyuscore2dollarsk!7 () Real)
(assert (= (+ (* 2 a) vyuscore6dollarsk!3 (* (- 1) (* xuscore6dollarsk!1 a))) (- 2)))
(assert (= (+ (* vxuscore6dollarsk!2 vxuscore6dollarsk!2) (* vyuscore6dollarsk!3 vyuscore6dollarsk!3)) 8))
(assert (= (+ (* 2 a) vxuscore6dollarsk!2 (* (- 4) buscore2dollarsk!5) (* a yuscore6dollarsk!0) (* 4 (* a buscore2dollarsk!5))) 2))
(assert (= stateuscore2dollarsk!4 2))
(assert (= vyuscore6dollarsk!3 (- 2)))
(assert (= vxuscore6dollarsk!2 2))
(assert (= (+ (* (- 4) buscore2dollarsk!5) (* xuscore6dollarsk!1 a) (* a yuscore6dollarsk!0) (* 4 (* a buscore2dollarsk!5))) 0))
(assert (= stateuscore2dollarsk!4 1))
(assert (= vx 2))
(assert (= vy (- 2)))
(assert (= x 0))
(assert (= y 0))
(assert (= b 0))
(assert (not (= (+ (* 2 a) vyuscore2dollarsk!7 (* (- 1) (* a xuscore2dollarsk!6))) (- 2))))
(assert (not (= (+ (* (- 4) a) (* 4 buscore2dollarsk!5) (* xuscore6dollarsk!1 a) (* (- 1) (* a yuscore6dollarsk!0)) (* (- 4) (* a buscore2dollarsk!5))) (- 4))))
(check-sat)
