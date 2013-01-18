(set-logic QF_NRA)
(set-info :source | hong's problem \sum x_i^2 < 1 and \prod x_i > 1 |)
(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(assert (not (>= (+ (* x_0 x_0) (* x_1 x_1) (* x_2 x_2) (* x_3 x_3)) 1)))
(assert (not (<= (* x_0 x_1 x_2 x_3) 1)))
(check-sat)
