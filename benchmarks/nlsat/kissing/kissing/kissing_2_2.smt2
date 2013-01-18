(set-logic QF_NRA)
(set-info :source | kissing problem: pack 2 spheres in 2 dimensions |)
(declare-fun x_0_0 () Real)
(declare-fun x_0_1 () Real)
(declare-fun x_1_0 () Real)
(declare-fun x_1_1 () Real)
(assert (= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1)) 1.))
(assert (= (+ (* x_1_0 x_1_0) (* x_1_1 x_1_1)) 1.))
(assert (>= (+ (* (- x_0_0 x_1_0) (- x_0_0 x_1_0)) (* (- x_0_1 x_1_1) (- x_0_1 x_1_1))) 1.))
(check-sat)
