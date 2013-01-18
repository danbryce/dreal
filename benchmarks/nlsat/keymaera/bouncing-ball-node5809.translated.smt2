(set-logic QF_NRA)
(declare-fun g () Real)
(declare-fun huscore2dollarsk!2 () Real)
(declare-fun vuscore2dollarsk!3 () Real)
(declare-fun t1uscore0dollarsk!0 () Real)
(declare-fun tuscore2dollarsk!1 () Real)
(declare-fun V () Real)
(declare-fun c () Real)
(declare-fun v () Real)
(declare-fun t () Real)
(declare-fun h () Real)
(assert (or (= g 0.0)
            (and (not (= g 0.0))
                 (not (= vuscore2dollarsk!3 0.0))
                 (or (>= vuscore2dollarsk!3 0.0) (>= g 0.0))
                 (or (<= vuscore2dollarsk!3 0.0) (<= g 0.0)))
            (and (not (= g 0.0))
                 (not (= (+ vuscore2dollarsk!3
                            (* (- 1.0) g t1uscore0dollarsk!0))
                         0.0))
                 (or (>= (+ vuscore2dollarsk!3
                            (* (- 1.0) g t1uscore0dollarsk!0))
                         0.0)
                     (<= g 0.0))
                 (or (<= (+ vuscore2dollarsk!3
                            (* (- 1.0) g t1uscore0dollarsk!0))
                         0.0)
                     (>= g 0.0)))
            (= g 0.0)
            (= (+ (* (/ 1.0 2.0) vuscore2dollarsk!3 vuscore2dollarsk!3)
                  (* g huscore2dollarsk!2))
               0.0)
            (and (not (<= (+ (* (/ 1.0 2.0)
                                vuscore2dollarsk!3
                                vuscore2dollarsk!3)
                             (* g huscore2dollarsk!2))
                          0.0))
                 (not (<= g 0.0)))
            (and (not (>= (+ (* (/ 1.0 2.0)
                                vuscore2dollarsk!3
                                vuscore2dollarsk!3)
                             (* g huscore2dollarsk!2))
                          0.0))
                 (not (>= g 0.0)))))
(assert (>= t1uscore0dollarsk!0 0.0))
(assert (= huscore2dollarsk!2
           (+ (* (/ 1.0 2.0) g tuscore2dollarsk!1 tuscore2dollarsk!1)
              (* tuscore2dollarsk!1 vuscore2dollarsk!3))))
(assert (>= huscore2dollarsk!2 0.0))
(assert (>= tuscore2dollarsk!1 0.0))
(assert (<= vuscore2dollarsk!3 (+ (* (- 1.0) g tuscore2dollarsk!1) V)))
(assert (not (<= g 0.0)))
(assert (<= 0.0 c))
(assert (not (<= 1.0 c)))
(assert (= h (+ (* (/ 1.0 2.0) g t t) (* t v))))
(assert (>= h 0.0))
(assert (>= t 0.0))
(assert (<= v (+ (* (- 1.0) g t) V)))
(assert (<= (+ t1uscore0dollarsk!0 tuscore2dollarsk!1) 0.0))
(assert (not (>= (+ huscore2dollarsk!2
                    (* (- (/ 1.0 2.0))
                       g
                       t1uscore0dollarsk!0
                       t1uscore0dollarsk!0)
                    (* t1uscore0dollarsk!0 vuscore2dollarsk!3))
                 0.0)))
(assert (or (not (>= t1uscore0dollarsk!0 0.0))
            (>= (+ huscore2dollarsk!2
                   (* t1uscore0dollarsk!0 vuscore2dollarsk!3)
                   (* (- (/ 1.0 2.0)) g t1uscore0dollarsk!0 t1uscore0dollarsk!0))
                0.0)))
(assert (or (not (>= t1uscore0dollarsk!0 0.0)) (>= huscore2dollarsk!2 0.0)))
(check-sat)
