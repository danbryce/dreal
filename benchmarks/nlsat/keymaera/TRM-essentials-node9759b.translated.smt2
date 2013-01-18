(set-logic QF_NRA)
(declare-fun protectedzone () Real)
(declare-fun y2uscore3dollarsk!2 () Real)
(declare-fun x2uscore3dollarsk!4 () Real)
(declare-fun y1uscore3dollarsk!3 () Real)
(declare-fun x1uscore3dollarsk!5 () Real)
(declare-fun y2uscore2dollarsk!9 () Real)
(declare-fun x2uscore2dollarsk!7 () Real)
(declare-fun y1uscore2dollarsk!8 () Real)
(declare-fun x1uscore2dollarsk!6 () Real)
(declare-fun y2 () Real)
(declare-fun x2 () Real)
(declare-fun y1 () Real)
(declare-fun x1 () Real)
(declare-fun omuscore3dollarsk!0 () Real)
(declare-fun c2uscore2dollarsk!1 () Real)
(assert (>= (+ (* (+ x1uscore3dollarsk!5 (* (- 1.0) y1uscore3dollarsk!3))
                  (+ x1uscore3dollarsk!5 (* (- 1.0) y1uscore3dollarsk!3)))
               (* (+ x2uscore3dollarsk!4 (* (- 1.0) y2uscore3dollarsk!2))
                  (+ x2uscore3dollarsk!4 (* (- 1.0) y2uscore3dollarsk!2))))
            (* protectedzone protectedzone)))
(assert (>= (+ (* (+ x1uscore2dollarsk!6 (* (- 1.0) y1uscore2dollarsk!8))
                  (+ x1uscore2dollarsk!6 (* (- 1.0) y1uscore2dollarsk!8)))
               (* (+ x2uscore2dollarsk!7 (* (- 1.0) y2uscore2dollarsk!9))
                  (+ x2uscore2dollarsk!7 (* (- 1.0) y2uscore2dollarsk!9))))
            (* protectedzone protectedzone)))
(assert (>= (+ (* (+ x1 (* (- 1.0) y1)) (+ x1 (* (- 1.0) y1)))
               (* (+ x2 (* (- 1.0) y2)) (+ x2 (* (- 1.0) y2))))
            (* protectedzone protectedzone)))
(assert (not (= (+ (* (- 1.0)
                      omuscore3dollarsk!0
                      (+ x2uscore3dollarsk!4 (* (- 1.0) c2uscore2dollarsk!1)))
                   (* omuscore3dollarsk!0
                      (+ y2uscore3dollarsk!2 (* (- 1.0) c2uscore2dollarsk!1))))
                (* (- 1.0)
                   omuscore3dollarsk!0
                   (+ x2uscore3dollarsk!4 (* (- 1.0) y2uscore3dollarsk!2))))))
(check-sat)
