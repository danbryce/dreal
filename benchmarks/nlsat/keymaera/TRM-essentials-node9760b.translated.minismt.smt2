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
(declare-fun c1uscore2dollarsk!1 () Real)
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore3dollarsk!3 y1uscore3dollarsk!3) (* (- 2) (* y1uscore3dollarsk!3 x1uscore3dollarsk!5)) (* x1uscore3dollarsk!5 x1uscore3dollarsk!5) (* y2uscore3dollarsk!2 y2uscore3dollarsk!2) (* (- 2) (* y2uscore3dollarsk!2 x2uscore3dollarsk!4)) (* x2uscore3dollarsk!4 x2uscore3dollarsk!4)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore2dollarsk!8 y1uscore2dollarsk!8) (* (- 2) (* y1uscore2dollarsk!8 x1uscore2dollarsk!6)) (* x1uscore2dollarsk!6 x1uscore2dollarsk!6) (* y2uscore2dollarsk!9 y2uscore2dollarsk!9) (* (- 2) (* y2uscore2dollarsk!9 x2uscore2dollarsk!7)) (* x2uscore2dollarsk!7 x2uscore2dollarsk!7)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1 y1) (* (- 2) (* y1 x1)) (* x1 x1) (* y2 y2) (* (- 2) (* y2 x2)) (* x2 x2)) 0))
(assert false)
(check-sat)
