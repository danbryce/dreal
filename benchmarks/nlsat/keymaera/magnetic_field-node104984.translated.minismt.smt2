(set-logic QF_NRA)
(declare-fun xuscore10dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun vyuscore10dollarsk!3 () Real)
(declare-fun vxuscore10dollarsk!2 () Real)
(declare-fun buscore2dollarsk!5 () Real)
(declare-fun yuscore10dollarsk!0 () Real)
(declare-fun stateuscore2dollarsk!4 () Real)
(declare-fun vyuscore2dollarsk!9 () Real)
(declare-fun vxuscore2dollarsk!8 () Real)
(declare-fun yuscore2dollarsk!6 () Real)
(declare-fun xuscore2dollarsk!7 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(assert (= (+ (* 2 a) vyuscore10dollarsk!3 (* (- 1) (* xuscore10dollarsk!1 a))) (- 2)))
(assert (= (+ (* vxuscore10dollarsk!2 vxuscore10dollarsk!2) (* vyuscore10dollarsk!3 vyuscore10dollarsk!3)) 8))
(assert (= (+ (* 2 a) vxuscore10dollarsk!2 (* (- 4) buscore2dollarsk!5) (* a yuscore10dollarsk!0) (* 4 (* a buscore2dollarsk!5))) 2))
(assert (= stateuscore2dollarsk!4 2))
(assert (= stateuscore2dollarsk!4 1))
(assert (= vyuscore2dollarsk!9 (- 2)))
(assert (= vxuscore2dollarsk!8 (- 2)))
(assert (= (+ (* (- 4) a) (* 4 buscore2dollarsk!5) (* (- 4) (* a buscore2dollarsk!5)) (* (- 1) (* a yuscore2dollarsk!6)) (* a xuscore2dollarsk!7)) (- 4)))
(assert (= vx 2))
(assert (= vy (- 2)))
(assert (= x 0))
(assert (= y 0))
(assert (= b 0))
(assert (not (= stateuscore2dollarsk!4 0)))
(assert (not (= vyuscore10dollarsk!3 (- 2))))
(check-sat)
