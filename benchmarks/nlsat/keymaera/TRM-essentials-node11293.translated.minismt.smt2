(set-logic QF_NRA)
(declare-fun protectedzone () Real)
(declare-fun y2uscore3dollarsk!3 () Real)
(declare-fun x2uscore3dollarsk!5 () Real)
(declare-fun y1uscore3dollarsk!4 () Real)
(declare-fun x1uscore3dollarsk!6 () Real)
(declare-fun y2uscore2dollarsk!10 () Real)
(declare-fun x2uscore2dollarsk!8 () Real)
(declare-fun y1uscore2dollarsk!9 () Real)
(declare-fun x1uscore2dollarsk!7 () Real)
(declare-fun y2 () Real)
(declare-fun x2 () Real)
(declare-fun y1 () Real)
(declare-fun x1 () Real)
(declare-fun omuscore3dollarsk!2 () Real)
(declare-fun e2uscore4dollarsk!0 () Real)
(declare-fun d2uscore4dollarsk!1 () Real)
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore3dollarsk!4 y1uscore3dollarsk!4) (* (- 2) (* y1uscore3dollarsk!4 x1uscore3dollarsk!6)) (* x1uscore3dollarsk!6 x1uscore3dollarsk!6) (* y2uscore3dollarsk!3 y2uscore3dollarsk!3) (* (- 2) (* y2uscore3dollarsk!3 x2uscore3dollarsk!5)) (* x2uscore3dollarsk!5 x2uscore3dollarsk!5)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore2dollarsk!9 y1uscore2dollarsk!9) (* (- 2) (* y1uscore2dollarsk!9 x1uscore2dollarsk!7)) (* x1uscore2dollarsk!7 x1uscore2dollarsk!7) (* y2uscore2dollarsk!10 y2uscore2dollarsk!10) (* (- 2) (* y2uscore2dollarsk!10 x2uscore2dollarsk!8)) (* x2uscore2dollarsk!8 x2uscore2dollarsk!8)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1 y1) (* (- 2) (* y1 x1)) (* x1 x1) (* y2 y2) (* (- 2) (* y2 x2)) (* x2 x2)) 0))
(assert false)
(check-sat)
