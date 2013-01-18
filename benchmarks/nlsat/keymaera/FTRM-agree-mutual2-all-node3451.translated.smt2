(set-logic QF_NRA)
(declare-fun e2 () Real)
(declare-fun e1 () Real)
(declare-fun ruscore1dollarsk!1 () Real)
(declare-fun omuscore1dollarsk!0 () Real)
(declare-fun d2 () Real)
(declare-fun d1 () Real)
(declare-fun luscore0dollarsk!2 () Real)
(declare-fun x2 () Real)
(declare-fun y2 () Real)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(assert (= (* omuscore1dollarsk!0
              omuscore1dollarsk!0
              ruscore1dollarsk!1
              ruscore1dollarsk!1)
           (+ (* e1 e1) (* e2 e2))))
(assert (= (* omuscore1dollarsk!0
              omuscore1dollarsk!0
              ruscore1dollarsk!1
              ruscore1dollarsk!1)
           (+ (* d1 d1) (* d2 d2))))
(assert (= (+ (* (+ y1 (* (- 1.0) x1) (* (- 1.0) d1 luscore0dollarsk!2))
                 (+ y1 (* (- 1.0) x1) (* (- 1.0) d1 luscore0dollarsk!2)))
              (* (+ y2 (* (- 1.0) x2) (* (- 1.0) d2 luscore0dollarsk!2))
                 (+ y2 (* (- 1.0) x2) (* (- 1.0) d2 luscore0dollarsk!2))))
           (* 3.0 ruscore1dollarsk!1 ruscore1dollarsk!1)))
(assert (= (+ (* d1 d1 luscore0dollarsk!2 luscore0dollarsk!2)
              (* d2 d2 luscore0dollarsk!2 luscore0dollarsk!2))
           (* 3.0 ruscore1dollarsk!1 ruscore1dollarsk!1)))
(assert (>= ruscore1dollarsk!1 0.0))
(assert (= (+ (* d1 d1) (* d2 d2)) (+ (* e1 e1) (* e2 e2))))
(assert (not (<= luscore0dollarsk!2 0.0)))
(assert (= (+ x1 (* d1 luscore0dollarsk!2)) (+ y1 (* e1 luscore0dollarsk!2))))
(assert (= (+ x2 (* d2 luscore0dollarsk!2)) (+ y2 (* e2 luscore0dollarsk!2))))
(assert (not (>= luscore0dollarsk!2 0.0)))
(check-sat)
