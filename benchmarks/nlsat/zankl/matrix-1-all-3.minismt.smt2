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
(declare-fun x17 () Real)
(declare-fun x7 () Real)
(declare-fun x14 () Real)
(declare-fun x4 () Real)
(declare-fun x11 () Real)
(declare-fun x1 () Real)
(declare-fun x18 () Real)
(declare-fun x8 () Real)
(declare-fun x15 () Real)
(declare-fun x5 () Real)
(declare-fun x12 () Real)
(declare-fun x2 () Real)
(declare-fun x9 () Real)
(declare-fun x16 () Real)
(assert (>= x6 0))
(assert (>= x13 0))
(assert (>= x3 0))
(assert (>= x10 0))
(assert (>= x0 0))
(assert (>= x17 0))
(assert (>= x7 0))
(assert (>= x14 0))
(assert (>= x4 0))
(assert (>= x11 0))
(assert (>= x1 0))
(assert (>= x18 0))
(assert (>= x8 0))
(assert (>= x15 0))
(assert (>= x5 0))
(assert (>= x12 0))
(assert (>= x2 0))
(assert (>= x9 0))
(assert (>= x16 0))
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (<= (+ (* x1 x2) (* x3 x1 x2)) 0)) (>= (+ (* x1 x2) (* x3 x1 x2)) 0)) (>= (+ (* (- 1) x1) (* x3 x3 x1)) 0)) (and (and (not (<= (+ (* x5 x2) (* x3 x5 x2)) 0)) (>= (+ (* x5 x2) (* x3 x5 x2)) 0)) (>= (+ (* (- 1) x5) (* x3 x3 x5)) 0))) (and (and (not (<= (+ x6 (* (- 1) x4) (* (- 1) (* x5 x2)) (* x7 x2)) 0)) (>= (+ x6 (* (- 1) x4) (* (- 1) (* x5 x2)) (* x7 x2)) 0)) (>= (+ (* x3 x7) (* (- 1) (* x3 x5))) 0))) (and (and (not (<= (+ x6 (* (- 1) x0) (* x7 x2) (* (- 1) (* x1 x2))) 0)) (>= (+ x6 (* (- 1) x0) (* x7 x2) (* (- 1) (* x1 x2))) 0)) (>= (+ (* x3 x7) (* (- 1) (* x3 x1))) 0))) (and (and (not (<= (+ (* x7 x2) (* (- 1) (* x7 x8)) (* (- 1) (* x7 x2 x9))) 0)) (>= (+ (* x7 x2) (* (- 1) (* x7 x8)) (* (- 1) (* x7 x2 x9))) 0)) (>= (+ (* x3 x7) (* (- 1) (* x3 x7 x9))) 0))) (and (not (<= (+ (* (- 1) x10) x8 (* x10 x9)) 0)) (>= (+ (* (- 1) x10) x8 (* x10 x9)) 0))) (and (not (<= (+ (* (- 1) x10) x8 (* x2 x9) (* x3 x10 x9)) 0)) (>= (+ (* (- 1) x10) x8 (* x2 x9) (* x3 x10 x9)) 0))) (and (and (not (<= (+ x8 (* (- 1) x2) (* (- 1) (* x3 x8)) (* x2 x9) (* x3 x2 x9)) 0)) (>= (+ x8 (* (- 1) x2) (* (- 1) (* x3 x8)) (* x2 x9) (* x3 x2 x9)) 0)) (>= (+ (* (- 1) (* x3 x9)) (* x3 x3 x9)) 0))) (and (not (<= (+ (* (- 1) x10) x11 (* x10 x12)) 0)) (>= (+ (* (- 1) x10) x11 (* x10 x12)) 0))) (and (not (<= (+ x11 (* (- 1) x2) (* (- 1) (* x3 x10)) (* x12 x2) (* x3 x10 x12)) 0)) (>= (+ x11 (* (- 1) x2) (* (- 1) (* x3 x10)) (* x12 x2) (* x3 x10 x12)) 0))) (and (and (not (<= (+ (* x12 x2) (* x3 x12 x2)) 0)) (>= (+ (* x12 x2) (* x3 x12 x2)) 0)) (>= (+ (* (- 1) x12) (* x3 x3 x12)) 0))) (and (not (<= (+ x13 (* (- 1) x15) (* x10 x14) (* (- 1) (* x17 x16)) (* (- 1) (* x10 x18))) 0)) (>= (+ x13 (* (- 1) x15) (* x10 x14) (* (- 1) (* x17 x16)) (* (- 1) (* x10 x18))) 0))) (and (and (not (<= (+ x13 (* (- 1) x15) (* x14 x2) (* (- 1) (* x13 x16)) (* (- 1) (* x11 x18)) (* (- 1) (* x14 x8 x16)) (* (- 1) (* x18 x12 x2)) (* (- 1) (* x14 x2 x9 x16))) 0)) (>= (+ x13 (* (- 1) x15) (* x14 x2) (* (- 1) (* x13 x16)) (* (- 1) (* x11 x18)) (* (- 1) (* x14 x8 x16)) (* (- 1) (* x18 x12 x2)) (* (- 1) (* x14 x2 x9 x16))) 0)) (>= (+ (* x3 x14) (* (- 1) (* x3 x18 x12)) (* (- 1) (* x3 x14 x9 x16))) 0))) (and (and (and (and (and (and (not (<= (+ (* x1 x2) (* x3 x1 x2)) 0)) (>= (+ (* x1 x2) (* x3 x1 x2)) 0)) (>= (+ (* (- 1) x1) (* x3 x3 x1)) 0)) (and (and (not (<= (+ (* x5 x2) (* x3 x5 x2)) 0)) (>= (+ (* x5 x2) (* x3 x5 x2)) 0)) (>= (+ (* (- 1) x5) (* x3 x3 x5)) 0))) (and (and (not (<= (+ x6 (* (- 1) x4) (* (- 1) (* x5 x2)) (* x7 x2)) 0)) (>= (+ x6 (* (- 1) x4) (* (- 1) (* x5 x2)) (* x7 x2)) 0)) (>= (+ (* x3 x7) (* (- 1) (* x3 x5))) 0))) (and (and (not (<= (+ x6 (* (- 1) x0) (* x7 x2) (* (- 1) (* x1 x2))) 0)) (>= (+ x6 (* (- 1) x0) (* x7 x2) (* (- 1) (* x1 x2))) 0)) (>= (+ (* x3 x7) (* (- 1) (* x3 x1))) 0))) (and (and (not (<= (+ (* x7 x2) (* (- 1) (* x7 x8)) (* (- 1) (* x7 x2 x9))) 0)) (>= (+ (* x7 x2) (* (- 1) (* x7 x8)) (* (- 1) (* x7 x2 x9))) 0)) (>= (+ (* x3 x7) (* (- 1) (* x3 x7 x9))) 0)))))
(exit)
(check-sat)
