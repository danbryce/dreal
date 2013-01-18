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
(assert (= (+ (* d1 d1) (* d2 d2)) (+ (* e1 e1) (* e2 e2))))
(assert (not (<= luscore0dollarsk!0 0.0)))
(assert (= (+ x1 (* d1 luscore0dollarsk!0)) (+ y1 (* e1 luscore0dollarsk!0))))
(assert (= (+ x2 (* d2 luscore0dollarsk!0)) (+ y2 (* e2 luscore0dollarsk!0))))
(assert (not (= (+ (* d1 d1 luscore0dollarsk!0 luscore0dollarsk!0)
                   (* d2 d2 luscore0dollarsk!0 luscore0dollarsk!0))
                (+ (* (+ y1 (* (- 1.0) x1) (* (- 1.0) d1 luscore0dollarsk!0))
                      (+ y1 (* (- 1.0) x1) (* (- 1.0) d1 luscore0dollarsk!0)))
                   (* (+ y2 (* (- 1.0) x2) (* (- 1.0) d2 luscore0dollarsk!0))
                      (+ y2 (* (- 1.0) x2) (* (- 1.0) d2 luscore0dollarsk!0)))))))
(check-sat)
