(set-logic QF_NRA)
(declare-fun c2uscore2dollarsk!17 () Real)
(declare-fun x2uscore4dollarsk!8 () Real)
(declare-fun omuscore3dollarsk!16 () Real)
(declare-fun d1uscore4dollarsk!10 () Real)
(declare-fun c1uscore2dollarsk!18 () Real)
(declare-fun x1uscore4dollarsk!9 () Real)
(declare-fun d2uscore4dollarsk!11 () Real)
(declare-fun y2uscore4dollarsk!4 () Real)
(declare-fun e1uscore4dollarsk!6 () Real)
(declare-fun y1uscore4dollarsk!5 () Real)
(declare-fun e2uscore4dollarsk!7 () Real)
(declare-fun z2uscore4dollarsk!0 () Real)
(declare-fun f1uscore4dollarsk!2 () Real)
(declare-fun z1uscore4dollarsk!1 () Real)
(declare-fun f2uscore4dollarsk!3 () Real)
(declare-fun u2uscore4dollarsk!12 () Real)
(declare-fun g1uscore4dollarsk!14 () Real)
(declare-fun u1uscore4dollarsk!13 () Real)
(declare-fun g2uscore4dollarsk!15 () Real)
(declare-fun protectedzone () Real)
(declare-fun y2uscore3dollarsk!23 () Real)
(declare-fun x2uscore3dollarsk!25 () Real)
(declare-fun y1uscore3dollarsk!24 () Real)
(declare-fun x1uscore3dollarsk!26 () Real)
(declare-fun z2uscore3dollarsk!21 () Real)
(declare-fun z1uscore3dollarsk!22 () Real)
(declare-fun u2uscore3dollarsk!19 () Real)
(declare-fun u1uscore3dollarsk!20 () Real)
(declare-fun y2uscore2dollarsk!34 () Real)
(declare-fun x2uscore2dollarsk!32 () Real)
(declare-fun y1uscore2dollarsk!33 () Real)
(declare-fun x1uscore2dollarsk!31 () Real)
(declare-fun z2uscore2dollarsk!30 () Real)
(declare-fun z1uscore2dollarsk!29 () Real)
(declare-fun u2uscore2dollarsk!28 () Real)
(declare-fun u1uscore2dollarsk!27 () Real)
(declare-fun y2 () Real)
(declare-fun x2 () Real)
(declare-fun y1 () Real)
(declare-fun x1 () Real)
(declare-fun z2 () Real)
(declare-fun z1 () Real)
(declare-fun u2 () Real)
(declare-fun u1 () Real)
(assert (= (+ d1uscore4dollarsk!10 (* (- 1) (* c2uscore2dollarsk!17 omuscore3dollarsk!16)) (* x2uscore4dollarsk!8 omuscore3dollarsk!16)) 0))
(assert (= (+ d2uscore4dollarsk!11 (* omuscore3dollarsk!16 c1uscore2dollarsk!18) (* (- 1) (* omuscore3dollarsk!16 x1uscore4dollarsk!9))) 0))
(assert (= (+ e1uscore4dollarsk!6 (* (- 1) (* c2uscore2dollarsk!17 omuscore3dollarsk!16)) (* omuscore3dollarsk!16 y2uscore4dollarsk!4)) 0))
(assert (= (+ e2uscore4dollarsk!7 (* omuscore3dollarsk!16 c1uscore2dollarsk!18) (* (- 1) (* omuscore3dollarsk!16 y1uscore4dollarsk!5))) 0))
(assert (= (+ f1uscore4dollarsk!2 (* (- 1) (* c2uscore2dollarsk!17 omuscore3dollarsk!16)) (* omuscore3dollarsk!16 z2uscore4dollarsk!0)) 0))
(assert (= (+ f2uscore4dollarsk!3 (* omuscore3dollarsk!16 c1uscore2dollarsk!18) (* (- 1) (* omuscore3dollarsk!16 z1uscore4dollarsk!1))) 0))
(assert (= (+ g1uscore4dollarsk!14 (* (- 1) (* c2uscore2dollarsk!17 omuscore3dollarsk!16)) (* omuscore3dollarsk!16 u2uscore4dollarsk!12)) 0))
(assert (= (+ g2uscore4dollarsk!15 (* omuscore3dollarsk!16 c1uscore2dollarsk!18) (* (- 1) (* omuscore3dollarsk!16 u1uscore4dollarsk!13))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore3dollarsk!24 y1uscore3dollarsk!24) (* (- 2) (* y1uscore3dollarsk!24 x1uscore3dollarsk!26)) (* x1uscore3dollarsk!26 x1uscore3dollarsk!26) (* y2uscore3dollarsk!23 y2uscore3dollarsk!23) (* (- 2) (* y2uscore3dollarsk!23 x2uscore3dollarsk!25)) (* x2uscore3dollarsk!25 x2uscore3dollarsk!25)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore3dollarsk!24 y1uscore3dollarsk!24) (* y2uscore3dollarsk!23 y2uscore3dollarsk!23) (* (- 2) (* y1uscore3dollarsk!24 z1uscore3dollarsk!22)) (* z1uscore3dollarsk!22 z1uscore3dollarsk!22) (* (- 2) (* y2uscore3dollarsk!23 z2uscore3dollarsk!21)) (* z2uscore3dollarsk!21 z2uscore3dollarsk!21)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* x1uscore3dollarsk!26 x1uscore3dollarsk!26) (* x2uscore3dollarsk!25 x2uscore3dollarsk!25) (* z1uscore3dollarsk!22 z1uscore3dollarsk!22) (* z2uscore3dollarsk!21 z2uscore3dollarsk!21) (* (- 2) (* x1uscore3dollarsk!26 z1uscore3dollarsk!22)) (* (- 2) (* x2uscore3dollarsk!25 z2uscore3dollarsk!21))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* x1uscore3dollarsk!26 x1uscore3dollarsk!26) (* x2uscore3dollarsk!25 x2uscore3dollarsk!25) (* (- 2) (* x1uscore3dollarsk!26 u1uscore3dollarsk!20)) (* u1uscore3dollarsk!20 u1uscore3dollarsk!20) (* (- 2) (* x2uscore3dollarsk!25 u2uscore3dollarsk!19)) (* u2uscore3dollarsk!19 u2uscore3dollarsk!19)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore3dollarsk!24 y1uscore3dollarsk!24) (* y2uscore3dollarsk!23 y2uscore3dollarsk!23) (* u1uscore3dollarsk!20 u1uscore3dollarsk!20) (* u2uscore3dollarsk!19 u2uscore3dollarsk!19) (* (- 2) (* y1uscore3dollarsk!24 u1uscore3dollarsk!20)) (* (- 2) (* y2uscore3dollarsk!23 u2uscore3dollarsk!19))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* z1uscore3dollarsk!22 z1uscore3dollarsk!22) (* z2uscore3dollarsk!21 z2uscore3dollarsk!21) (* u1uscore3dollarsk!20 u1uscore3dollarsk!20) (* u2uscore3dollarsk!19 u2uscore3dollarsk!19) (* (- 2) (* z1uscore3dollarsk!22 u1uscore3dollarsk!20)) (* (- 2) (* z2uscore3dollarsk!21 u2uscore3dollarsk!19))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore2dollarsk!33 y1uscore2dollarsk!33) (* (- 2) (* y1uscore2dollarsk!33 x1uscore2dollarsk!31)) (* x1uscore2dollarsk!31 x1uscore2dollarsk!31) (* y2uscore2dollarsk!34 y2uscore2dollarsk!34) (* (- 2) (* y2uscore2dollarsk!34 x2uscore2dollarsk!32)) (* x2uscore2dollarsk!32 x2uscore2dollarsk!32)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore2dollarsk!33 y1uscore2dollarsk!33) (* y2uscore2dollarsk!34 y2uscore2dollarsk!34) (* (- 2) (* y1uscore2dollarsk!33 z1uscore2dollarsk!29)) (* z1uscore2dollarsk!29 z1uscore2dollarsk!29) (* (- 2) (* y2uscore2dollarsk!34 z2uscore2dollarsk!30)) (* z2uscore2dollarsk!30 z2uscore2dollarsk!30)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* x1uscore2dollarsk!31 x1uscore2dollarsk!31) (* x2uscore2dollarsk!32 x2uscore2dollarsk!32) (* z1uscore2dollarsk!29 z1uscore2dollarsk!29) (* z2uscore2dollarsk!30 z2uscore2dollarsk!30) (* (- 2) (* x1uscore2dollarsk!31 z1uscore2dollarsk!29)) (* (- 2) (* x2uscore2dollarsk!32 z2uscore2dollarsk!30))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* x1uscore2dollarsk!31 x1uscore2dollarsk!31) (* x2uscore2dollarsk!32 x2uscore2dollarsk!32) (* (- 2) (* x1uscore2dollarsk!31 u1uscore2dollarsk!27)) (* u1uscore2dollarsk!27 u1uscore2dollarsk!27) (* (- 2) (* x2uscore2dollarsk!32 u2uscore2dollarsk!28)) (* u2uscore2dollarsk!28 u2uscore2dollarsk!28)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1uscore2dollarsk!33 y1uscore2dollarsk!33) (* y2uscore2dollarsk!34 y2uscore2dollarsk!34) (* u1uscore2dollarsk!27 u1uscore2dollarsk!27) (* u2uscore2dollarsk!28 u2uscore2dollarsk!28) (* (- 2) (* y1uscore2dollarsk!33 u1uscore2dollarsk!27)) (* (- 2) (* y2uscore2dollarsk!34 u2uscore2dollarsk!28))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* z1uscore2dollarsk!29 z1uscore2dollarsk!29) (* z2uscore2dollarsk!30 z2uscore2dollarsk!30) (* u1uscore2dollarsk!27 u1uscore2dollarsk!27) (* u2uscore2dollarsk!28 u2uscore2dollarsk!28) (* (- 2) (* z1uscore2dollarsk!29 u1uscore2dollarsk!27)) (* (- 2) (* z2uscore2dollarsk!30 u2uscore2dollarsk!28))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1 y1) (* (- 2) (* y1 x1)) (* x1 x1) (* y2 y2) (* (- 2) (* y2 x2)) (* x2 x2)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1 y1) (* y2 y2) (* (- 2) (* y1 z1)) (* z1 z1) (* (- 2) (* y2 z2)) (* z2 z2)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* x1 x1) (* x2 x2) (* z1 z1) (* z2 z2) (* (- 2) (* x1 z1)) (* (- 2) (* x2 z2))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* x1 x1) (* x2 x2) (* (- 2) (* x1 u1)) (* u1 u1) (* (- 2) (* x2 u2)) (* u2 u2)) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* y1 y1) (* y2 y2) (* u1 u1) (* u2 u2) (* (- 2) (* y1 u1)) (* (- 2) (* y2 u2))) 0))
(assert (>= (+ (* (- 1) (* protectedzone protectedzone)) (* z1 z1) (* z2 z2) (* u1 u1) (* u2 u2) (* (- 2) (* z1 u1)) (* (- 2) (* z2 u2))) 0))
(assert (not (>= (+ (* 2 (* d1uscore4dollarsk!10 x1uscore4dollarsk!9)) (* (- 2) (* x1uscore4dollarsk!9 f1uscore4dollarsk!2)) (* (- 2) (* d1uscore4dollarsk!10 z1uscore4dollarsk!1)) (* 2 (* f1uscore4dollarsk!2 z1uscore4dollarsk!1)) (* 2 (* x2uscore4dollarsk!8 d2uscore4dollarsk!11)) (* (- 2) (* x2uscore4dollarsk!8 f2uscore4dollarsk!3)) (* (- 2) (* d2uscore4dollarsk!11 z2uscore4dollarsk!0)) (* 2 (* z2uscore4dollarsk!0 f2uscore4dollarsk!3))) 0)))
(check-sat)
