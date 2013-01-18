(set-logic QF_NRA)
(set-info :source | kissing problem: pack 5 spheres in 3 dimensions |)
(declare-fun x_0_0 () Real)
(declare-fun x_0_1 () Real)
(declare-fun x_0_2 () Real)
(declare-fun x_1_0 () Real)
(declare-fun x_1_1 () Real)
(declare-fun x_1_2 () Real)
(declare-fun x_2_0 () Real)
(declare-fun x_2_1 () Real)
(declare-fun x_2_2 () Real)
(declare-fun x_3_0 () Real)
(declare-fun x_3_1 () Real)
(declare-fun x_3_2 () Real)
(declare-fun x_4_0 () Real)
(declare-fun x_4_1 () Real)
(declare-fun x_4_2 () Real)
(assert (= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1) (* x_0_2 x_0_2)) 1))
(assert (= (+ (* x_1_0 x_1_0) (* x_1_1 x_1_1) (* x_1_2 x_1_2)) 1))
(assert (= (+ (* x_2_0 x_2_0) (* x_2_1 x_2_1) (* x_2_2 x_2_2)) 1))
(assert (= (+ (* x_3_0 x_3_0) (* x_3_1 x_3_1) (* x_3_2 x_3_2)) 1))
(assert (= (+ (* x_4_0 x_4_0) (* x_4_1 x_4_1) (* x_4_2 x_4_2)) 1))
(assert (>= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1) (* x_0_2 x_0_2) (* x_1_0 x_1_0) (* x_1_1 x_1_1) (* x_1_2 x_1_2) (* (- 2) (* x_0_0 x_1_0)) (* (- 2) (* x_0_1 x_1_1)) (* (- 2) (* x_0_2 x_1_2))) 1))
(assert (>= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1) (* x_0_2 x_0_2) (* x_2_0 x_2_0) (* x_2_1 x_2_1) (* x_2_2 x_2_2) (* (- 2) (* x_0_0 x_2_0)) (* (- 2) (* x_0_1 x_2_1)) (* (- 2) (* x_0_2 x_2_2))) 1))
(assert (>= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1) (* x_0_2 x_0_2) (* x_3_0 x_3_0) (* x_3_1 x_3_1) (* x_3_2 x_3_2) (* (- 2) (* x_0_0 x_3_0)) (* (- 2) (* x_0_1 x_3_1)) (* (- 2) (* x_0_2 x_3_2))) 1))
(assert (>= (+ (* x_0_0 x_0_0) (* x_0_1 x_0_1) (* x_0_2 x_0_2) (* x_4_0 x_4_0) (* x_4_1 x_4_1) (* x_4_2 x_4_2) (* (- 2) (* x_0_0 x_4_0)) (* (- 2) (* x_0_1 x_4_1)) (* (- 2) (* x_0_2 x_4_2))) 1))
(assert (>= (+ (* x_1_0 x_1_0) (* x_1_1 x_1_1) (* x_1_2 x_1_2) (* x_2_0 x_2_0) (* x_2_1 x_2_1) (* x_2_2 x_2_2) (* (- 2) (* x_1_0 x_2_0)) (* (- 2) (* x_1_1 x_2_1)) (* (- 2) (* x_1_2 x_2_2))) 1))
(assert (>= (+ (* x_1_0 x_1_0) (* x_1_1 x_1_1) (* x_1_2 x_1_2) (* x_3_0 x_3_0) (* x_3_1 x_3_1) (* x_3_2 x_3_2) (* (- 2) (* x_1_0 x_3_0)) (* (- 2) (* x_1_1 x_3_1)) (* (- 2) (* x_1_2 x_3_2))) 1))
(assert (>= (+ (* x_1_0 x_1_0) (* x_1_1 x_1_1) (* x_1_2 x_1_2) (* x_4_0 x_4_0) (* x_4_1 x_4_1) (* x_4_2 x_4_2) (* (- 2) (* x_1_0 x_4_0)) (* (- 2) (* x_1_1 x_4_1)) (* (- 2) (* x_1_2 x_4_2))) 1))
(assert (>= (+ (* x_2_0 x_2_0) (* x_2_1 x_2_1) (* x_2_2 x_2_2) (* x_3_0 x_3_0) (* x_3_1 x_3_1) (* x_3_2 x_3_2) (* (- 2) (* x_2_0 x_3_0)) (* (- 2) (* x_2_1 x_3_1)) (* (- 2) (* x_2_2 x_3_2))) 1))
(assert (>= (+ (* x_2_0 x_2_0) (* x_2_1 x_2_1) (* x_2_2 x_2_2) (* x_4_0 x_4_0) (* x_4_1 x_4_1) (* x_4_2 x_4_2) (* (- 2) (* x_2_0 x_4_0)) (* (- 2) (* x_2_1 x_4_1)) (* (- 2) (* x_2_2 x_4_2))) 1))
(assert (>= (+ (* x_3_0 x_3_0) (* x_3_1 x_3_1) (* x_3_2 x_3_2) (* x_4_0 x_4_0) (* x_4_1 x_4_1) (* x_4_2 x_4_2) (* (- 2) (* x_3_0 x_4_0)) (* (- 2) (* x_3_1 x_4_1)) (* (- 2) (* x_3_2 x_4_2))) 1))
(check-sat)
