(set-logic QF_NRA)
(declare-fun N () Real)
(declare-fun nuscore2dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!1 () Real)
(declare-fun yuscore2dollarsk!2 () Real)
(declare-fun zuscore2dollarsk!3 () Real)
(assert (<= nuscore2dollarsk!0 N))
(assert (= (* nuscore2dollarsk!0 nuscore2dollarsk!0 nuscore2dollarsk!0)
           xuscore2dollarsk!1))
(assert (= (+ (* 3.0 nuscore2dollarsk!0) (* 3.0 nuscore2dollarsk!0 nuscore2dollarsk!0))
           (+ (- 1.0) yuscore2dollarsk!2)))
(assert (= (* 6.0 nuscore2dollarsk!0) (+ (- 6.0) zuscore2dollarsk!3)))
(assert (not (= (+ (* 3.0 nuscore2dollarsk!0)
                   (* 3.0 (+ 1.0 nuscore2dollarsk!0) (+ 1.0 nuscore2dollarsk!0)))
                (+ (- 4.0) yuscore2dollarsk!2 zuscore2dollarsk!3))))
(check-sat)
