(set-logic QF_NRA)
(declare-fun zuscore2dollarsk!2 () Real)
(declare-fun yuscore2dollarsk!0 () Real)
(declare-fun xuscore2dollarsk!1 () Real)
(declare-fun e () Real)
(assert (= (* 3.0 xuscore2dollarsk!1)
           (+ (- 3.0)
              (* 3.0 yuscore2dollarsk!0)
              (* zuscore2dollarsk!2
                 (+ 2.0
                    (* 3.0 zuscore2dollarsk!2)
                    (* zuscore2dollarsk!2 zuscore2dollarsk!2))))))
(assert (not (= e 0.0)))
(assert (not (= (+ (* 3.0 xuscore2dollarsk!1) (* (- 3.0) zuscore2dollarsk!2))
                (+ (- 3.0)
                   (* 3.0 yuscore2dollarsk!0)
                   (* 3.0 zuscore2dollarsk!2 zuscore2dollarsk!2)
                   (* (+ (- 1.0) zuscore2dollarsk!2)
                      (+ (- 1.0)
                         (* 3.0 zuscore2dollarsk!2)
                         (* (+ (- 1.0) zuscore2dollarsk!2)
                            (+ (- 1.0) zuscore2dollarsk!2))))))))
(check-sat)
