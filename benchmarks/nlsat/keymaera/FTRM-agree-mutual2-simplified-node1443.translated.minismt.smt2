(set-logic QF_NRA)
(declare-fun e2 () Real)
(declare-fun e1 () Real)
(declare-fun d2 () Real)
(declare-fun d1 () Real)
(declare-fun luscore0dollarsk!0 () Real)
(declare-fun y1 () Real)
(declare-fun x1 () Real)
(declare-fun y2 () Real)
(declare-fun x2 () Real)
(assert (= (+ (* d1 d1) (* d2 d2) (* (- 1) (* e1 e1)) (* (- 1) (* e2 e2))) 0))
(assert (not (<= luscore0dollarsk!0 0)))
(assert (= (+ (* (- 1) y1) x1 (* d1 luscore0dollarsk!0) (* (- 1) (* e1 luscore0dollarsk!0))) 0))
(assert (= (+ (* (- 1) y2) x2 (* d2 luscore0dollarsk!0) (* (- 1) (* e2 luscore0dollarsk!0))) 0))
(assert (not (= (+ (* (- 1) (* y1 y1)) (* 2 (* y1 x1)) (* (- 1) (* x1 x1)) (* (- 1) (* y2 y2)) (* 2 (* y2 x2)) (* (- 1) (* x2 x2)) (* 2 (* d1 luscore0dollarsk!0 y1)) (* (- 2) (* d1 luscore0dollarsk!0 x1)) (* 2 (* d2 luscore0dollarsk!0 y2)) (* (- 2) (* d2 luscore0dollarsk!0 x2))) 0)))
(check-sat)
