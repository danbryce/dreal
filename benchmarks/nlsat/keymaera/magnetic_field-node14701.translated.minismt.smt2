(set-logic QF_NRA)
(declare-fun xuscore3dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun vyuscore3dollarsk!3 () Real)
(declare-fun vxuscore3dollarsk!2 () Real)
(declare-fun buscore2dollarsk!5 () Real)
(declare-fun yuscore3dollarsk!0 () Real)
(declare-fun stateuscore2dollarsk!4 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(declare-fun vyuscore2dollarsk!6 () Real)
(assert (= (+ (* 2 a) vyuscore3dollarsk!3 (* (- 1) (* xuscore3dollarsk!1 a))) (- 2)))
(assert (= (+ (* vxuscore3dollarsk!2 vxuscore3dollarsk!2) (* vyuscore3dollarsk!3 vyuscore3dollarsk!3)) 8))
(assert (= (+ (* 2 a) vxuscore3dollarsk!2 (* (- 4) buscore2dollarsk!5) (* a yuscore3dollarsk!0) (* 4 (* a buscore2dollarsk!5))) 2))
(assert (= stateuscore2dollarsk!4 2))
(assert (= vyuscore3dollarsk!3 (- 2)))
(assert (= vxuscore3dollarsk!2 2))
(assert (= (+ (* (- 4) buscore2dollarsk!5) (* xuscore3dollarsk!1 a) (* a yuscore3dollarsk!0) (* 4 (* a buscore2dollarsk!5))) 0))
(assert (= stateuscore2dollarsk!4 1))
(assert (= stateuscore2dollarsk!4 0))
(assert (= vx 2))
(assert (= vy (- 2)))
(assert (= x 0))
(assert (= y 0))
(assert (= b 0))
(assert (not (= vyuscore2dollarsk!6 (- 2))))
(assert (not (= vxuscore3dollarsk!2 (- 2))))
(check-sat)
