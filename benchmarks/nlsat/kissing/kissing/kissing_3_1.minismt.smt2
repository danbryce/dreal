(set-logic QF_NRA)
(set-info :source | kissing problem: pack 1 spheres in 3 dimensions |)
(declare-fun x_0_0 () Real)
(declare-fun x_0_1 () Real)
(declare-fun x_0_2 () Real)
(assert (= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1) (* x_0_2 x_0_2)) 1))
(check-sat)
