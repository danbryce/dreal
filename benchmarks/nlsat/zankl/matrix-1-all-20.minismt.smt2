(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x6 () Real)
(declare-fun x13 () Real)
(declare-fun x3 () Real)
(declare-fun x10 () Real)
(declare-fun x0 () Real)
(declare-fun x7 () Real)
(declare-fun x14 () Real)
(declare-fun x4 () Real)
(declare-fun x11 () Real)
(declare-fun x1 () Real)
(declare-fun x8 () Real)
(declare-fun x15 () Real)
(declare-fun x5 () Real)
(declare-fun x12 () Real)
(declare-fun x2 () Real)
(declare-fun x9 () Real)
(assert (>= x6 0))
(assert (>= x13 0))
(assert (>= x3 0))
(assert (>= x10 0))
(assert (>= x0 0))
(assert (>= x7 0))
(assert (>= x14 0))
(assert (>= x4 0))
(assert (>= x11 0))
(assert (>= x1 0))
(assert (>= x8 0))
(assert (>= x15 0))
(assert (>= x5 0))
(assert (>= x12 0))
(assert (>= x2 0))
(assert (>= x9 0))
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (not (<= (+ (* x1 x2) (* (- 1) (* x3 x1)) (* (- 1) (* x4 x1 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x3 x1)) (* (- 1) (* x4 x1 x2))) 0)) (and (not (<= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* x4 x1 x2) (* (- 1) (* x6 x7 x1))) 0)) (>= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* x4 x1 x2) (* (- 1) (* x6 x7 x1))) 0))) (and (not (<= (+ (* x1 x2) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2))) 0))) (and (not (<= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2)) (* x7 x4 x1)) 0)) (>= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2)) (* x7 x4 x1)) 0))) (and (and (not (<= (* x10 x9) 0)) (>= (* x10 x9) 0)) (>= (+ (* (- 1) x9) (* x11 x9)) 0))) (and (not (<= (+ (* x13 x2) (* (- 1) (* x13 x3)) (* (- 1) (* x13 x4 x2))) 0)) (>= (+ (* x13 x2) (* (- 1) (* x13 x3)) (* (- 1) (* x13 x4 x2))) 0))) (and (and (not (<= (+ x12 (* x13 x3)) 0)) (>= (+ x12 (* x13 x3)) 0)) (>= (* x13 x4) 1))) (and (not (<= (+ (* x13 x3) (* (- 1) (* x13 x5)) (* x13 x4 x2) (* (- 1) (* x6 x13 x7))) 0)) (>= (+ (* x13 x3) (* (- 1) (* x13 x5)) (* x13 x4 x2) (* (- 1) (* x6 x13 x7))) 0))) (and (not (<= (+ (* x13 x2) (* (- 1) (* x13 x5)) (* (- 1) (* x6 x13 x2))) 0)) (>= (+ (* x13 x2) (* (- 1) (* x13 x5)) (* (- 1) (* x6 x13 x2))) 0))) (and (and (not (<= (+ x12 (* x13 x5)) 0)) (>= (+ x12 (* x13 x5)) 0)) (>= (* x6 x13) 1))) (and (not (<= (+ (* x13 x3) (* (- 1) (* x13 x5)) (* (- 1) (* x6 x13 x2)) (* x13 x7 x4)) 0)) (>= (+ (* x13 x3) (* (- 1) (* x13 x5)) (* (- 1) (* x6 x13 x2)) (* x13 x7 x4)) 0))) (and (and (not (<= (* x10 x15) 0)) (>= (* x10 x15) 0)) (>= (+ (* (- 1) x15) (* x11 x15)) 0))) (and (and (and (and (and (not (<= (+ (* x1 x2) (* (- 1) (* x3 x1)) (* (- 1) (* x4 x1 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x3 x1)) (* (- 1) (* x4 x1 x2))) 0)) (and (not (<= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* x4 x1 x2) (* (- 1) (* x6 x7 x1))) 0)) (>= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* x4 x1 x2) (* (- 1) (* x6 x7 x1))) 0))) (and (not (<= (+ (* x1 x2) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2))) 0))) (and (not (<= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2)) (* x7 x4 x1)) 0)) (>= (+ (* x3 x1) (* (- 1) (* x1 x5)) (* (- 1) (* x6 x1 x2)) (* x7 x4 x1)) 0))) (and (and (not (<= (* x10 x9) 0)) (>= (* x10 x9) 0)) (>= (+ (* (- 1) x9) (* x11 x9)) 0)))))
(exit)
(check-sat)
