(set-logic QF_NRA)
(declare-fun yuscore2dollarsk!1 () Real)
(declare-fun xuscore2dollarsk!0 () Real)
(declare-fun vuscore2dollarsk!3 () Real)
(declare-fun uuscore2dollarsk!2 () Real)
(declare-fun b () Real)
(declare-fun a () Real)
(assert (not (= xuscore2dollarsk!0 yuscore2dollarsk!1)))
(assert (= (* 2.0 a b)
           (+ (* uuscore2dollarsk!2 xuscore2dollarsk!0)
              (* vuscore2dollarsk!3 yuscore2dollarsk!1))))
(assert (<= xuscore2dollarsk!0 yuscore2dollarsk!1))
(assert (not (= (* 2.0 a b)
                (+ (* xuscore2dollarsk!0
                      (+ uuscore2dollarsk!2 vuscore2dollarsk!3))
                   (* vuscore2dollarsk!3
                      (+ yuscore2dollarsk!1 (* (- 1.0) xuscore2dollarsk!0)))))))
(check-sat)
