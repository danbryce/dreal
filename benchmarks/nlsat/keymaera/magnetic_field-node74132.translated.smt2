(set-logic QF_NRA)
(declare-fun xuscore7dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun vyuscore7dollarsk!3 () Real)
(declare-fun vxuscore7dollarsk!2 () Real)
(declare-fun buscore2dollarsk!5 () Real)
(declare-fun yuscore7dollarsk!0 () Real)
(declare-fun stateuscore2dollarsk!4 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(declare-fun vyuscore2dollarsk!7 () Real)
(declare-fun vxuscore2dollarsk!6 () Real)
(assert (= vyuscore7dollarsk!3 (+ (- 2.0) (* a (+ (- 2.0) xuscore7dollarsk!1)))))
(assert (= (+ (* vxuscore7dollarsk!2 vxuscore7dollarsk!2)
              (* vyuscore7dollarsk!3 vyuscore7dollarsk!3))
           8.0))
(assert (= vxuscore7dollarsk!2
           (+ 2.0
              (* (- 1.0) a (+ 2.0 yuscore7dollarsk!0))
              (* 4.0 buscore2dollarsk!5 (+ 1.0 (* (- 1.0) a))))))
(assert (= stateuscore2dollarsk!4 2.0))
(assert (= stateuscore2dollarsk!4 1.0))
(assert (= vx 2.0))
(assert (= vy (- 2.0)))
(assert (= x 0.0))
(assert (= y 0.0))
(assert (= b 0.0))
(assert (not (= stateuscore2dollarsk!4 0.0)))
(assert (not (= (+ (* vxuscore2dollarsk!6 vxuscore2dollarsk!6)
                   (* vyuscore2dollarsk!7 vyuscore2dollarsk!7))
                8.0)))
(assert (not (= (* a (+ xuscore7dollarsk!1 (* (- 1.0) yuscore7dollarsk!0)))
                (* (+ (- 4.0) (* (- 4.0) buscore2dollarsk!5))
                   (+ 1.0 (* (- 1.0) a))))))
(check-sat)
