(set-logic QF_NRA)
(declare-fun muscore1dollarsk!0 () Real)
(declare-fun zuscore1dollarsk!1 () Real)
(declare-fun b () Real)
(declare-fun duscore1dollarsk!2 () Real)
(declare-fun vuscore1dollarsk!3 () Real)
(declare-fun z () Real)
(declare-fun m () Real)
(declare-fun d () Real)
(declare-fun v () Real)
(declare-fun A () Real)
(declare-fun ep () Real)
(assert (>= (+ (* (- 1) muscore1dollarsk!0) zuscore1dollarsk!1) 0))
(assert (<= (+ (* vuscore1dollarsk!3 vuscore1dollarsk!3) (* (- 1) (* duscore1dollarsk!2 duscore1dollarsk!2)) (* (- 2) (* muscore1dollarsk!0 b)) (* 2 (* zuscore1dollarsk!1 b))) 0))
(assert (>= duscore1dollarsk!2 0))
(assert (<= (+ (* v v) (* (- 1) (* d d)) (* 2 (* b z)) (* (- 2) (* b m))) 0))
(assert (>= d 0))
(assert (not (<= b 0)))
(assert (>= A 0))
(assert (>= ep 0))
(assert (not (<= (+ (* (- 1) duscore1dollarsk!2) vuscore1dollarsk!3) 0)))
(check-sat)
