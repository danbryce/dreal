(set-logic QF_NRA)
(declare-fun tcuscore2dollarsk!2 () Real)
(declare-fun t3uscore0dollarsk!0 () Real)
(declare-fun tuscore2dollarsk!3 () Real)
(declare-fun moduscore2dollarsk!1 () Real)
(declare-fun t () Real)
(declare-fun kmod () Real)
(declare-fun v () Real)
(declare-fun u () Real)
(declare-fun tc () Real)
(declare-fun s () Real)
(declare-fun cmax () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun k () Real)
(assert (or (and (>= tcuscore2dollarsk!2 1.0) (not (= tcuscore2dollarsk!2 1.0)))
            (<= (+ t3uscore0dollarsk!0 tcuscore2dollarsk!2) 1.0)))
(assert (>= t3uscore0dollarsk!0 0.0))
(assert (not (<= 10.0 tuscore2dollarsk!3)))
(assert (= moduscore2dollarsk!1 2.0))
(assert (not (<= 1.0 tcuscore2dollarsk!2)))
(assert (<= tuscore2dollarsk!3 10.0))
(assert (<= tcuscore2dollarsk!2 1.0))
(assert (>= 1.0 t))
(assert (>= t 0.0))
(assert (= kmod 1.0))
(assert (= (+ (* u u) (* v v)) 1.0))
(assert (= tc 0.0))
(assert (= s 1.0))
(assert (= cmax 100.0))
(assert (<= (- 100.0) x))
(assert (<= x 100.0))
(assert (<= (- 100.0) y))
(assert (<= y 100.0))
(assert (= k 1.0))
(assert (not (<= (+ t3uscore0dollarsk!0 tcuscore2dollarsk!2) 1.0)))
(assert (or (not (>= t3uscore0dollarsk!0 0.0))
            (and (<= (+ t3uscore0dollarsk!0 tuscore2dollarsk!3) 10.0)
                 (<= (+ t3uscore0dollarsk!0 tcuscore2dollarsk!2) 1.0))))
(assert (or (and (>= tuscore2dollarsk!3 10.0) (not (= tuscore2dollarsk!3 10.0)))
            (<= (+ t3uscore0dollarsk!0 tuscore2dollarsk!3) 10.0)))
(assert (or (not (>= t3uscore0dollarsk!0 0.0))
            (and (<= tuscore2dollarsk!3 10.0) (<= tcuscore2dollarsk!2 1.0))))
(check-sat)
