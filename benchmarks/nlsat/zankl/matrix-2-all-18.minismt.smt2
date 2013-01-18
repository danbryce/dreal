(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x6 () Real)
(declare-fun x23 () Real)
(declare-fun x13 () Real)
(declare-fun x3 () Real)
(declare-fun x20 () Real)
(declare-fun x10 () Real)
(declare-fun x0 () Real)
(declare-fun x17 () Real)
(declare-fun x7 () Real)
(declare-fun x24 () Real)
(declare-fun x14 () Real)
(declare-fun x4 () Real)
(declare-fun x21 () Real)
(declare-fun x11 () Real)
(declare-fun x1 () Real)
(declare-fun x18 () Real)
(declare-fun x8 () Real)
(declare-fun x25 () Real)
(declare-fun x15 () Real)
(declare-fun x5 () Real)
(declare-fun x22 () Real)
(declare-fun x12 () Real)
(declare-fun x2 () Real)
(declare-fun x19 () Real)
(declare-fun x9 () Real)
(declare-fun x16 () Real)
(assert (>= x6 0))
(assert (>= x23 0))
(assert (>= x13 0))
(assert (>= x3 0))
(assert (>= x20 0))
(assert (>= x10 0))
(assert (>= x0 0))
(assert (>= x17 0))
(assert (>= x7 0))
(assert (>= x24 0))
(assert (>= x14 0))
(assert (>= x4 0))
(assert (>= x21 0))
(assert (>= x11 0))
(assert (>= x1 0))
(assert (>= x18 0))
(assert (>= x8 0))
(assert (>= x25 0))
(assert (>= x15 0))
(assert (>= x5 0))
(assert (>= x22 0))
(assert (>= x12 0))
(assert (>= x2 0))
(assert (>= x19 0))
(assert (>= x9 0))
(assert (>= x16 0))
(assert (and (and (and (and (and (and (and (not (<= (+ x0 (* (- 1) x9) (* x3 x1) (* x4 x2) (* (- 1) (* x3 x10)) (* (- 1) (* x4 x11))) 0)) (>= (+ x0 (* (- 1) x9) (* x3 x1) (* x4 x2) (* (- 1) (* x3 x10)) (* (- 1) (* x4 x11))) 0)) (and (>= (+ (* x1 x5) (* (- 1) (* x10 x5)) (* x7 x2) (* (- 1) (* x7 x11))) 0) (>= (+ (* (- 1) (* x11 x8)) (* x6 x1) (* x8 x2) (* (- 1) (* x6 x10))) 0))) (and (and (not (<= (+ (* x3 x1) (* x4 x2) (* (- 1) (* x1 x12)) (* (- 1) (* x13 x2)) (* (- 1) (* x3 x14 x1)) (* (- 1) (* x4 x1 x15)) (* (- 1) (* x17 x4 x2)) (* (- 1) (* x3 x2 x16))) 0)) (>= (+ (* x3 x1) (* x4 x2) (* (- 1) (* x1 x12)) (* (- 1) (* x13 x2)) (* (- 1) (* x3 x14 x1)) (* (- 1) (* x4 x1 x15)) (* (- 1) (* x17 x4 x2)) (* (- 1) (* x3 x2 x16))) 0)) (and (>= (+ (* x1 x5) (* x7 x2) (* (- 1) (* x14 x1 x5)) (* (- 1) (* x7 x1 x15)) (* (- 1) (* x17 x7 x2)) (* (- 1) (* x5 x2 x16))) 0) (>= (+ (* x6 x1) (* x8 x2) (* (- 1) (* x6 x14 x1)) (* (- 1) (* x1 x8 x15)) (* (- 1) (* x17 x8 x2)) (* (- 1) (* x6 x2 x16))) 0)))) (and (and (not (<= (+ (* (- 1) x3) x18 (* x3 x20) (* x4 x21) (* (- 1) (* x3 x5)) (* (- 1) (* x6 x4)) (* (- 1) (* x18 x5 x5)) (* (- 1) (* x6 x5 x19)) (* (- 1) (* x6 x7 x18)) (* (- 1) (* x6 x8 x19)) (* (- 1) (* x20 x5 x5 x12)) (* (- 1) (* x13 x21 x5 x5)) (* (- 1) (* x6 x5 x22 x12)) (* (- 1) (* x6 x23 x13 x5)) (* (- 1) (* x6 x20 x7 x12)) (* (- 1) (* x6 x13 x7 x21)) (* (- 1) (* x6 x8 x22 x12)) (* (- 1) (* x6 x23 x13 x8)) (* (- 1) (* x3 x20 x14 x5 x5)) (* (- 1) (* x20 x4 x15 x5 x5)) (* (- 1) (* x17 x4 x21 x5 x5)) (* (- 1) (* x3 x21 x5 x5 x16)) (* (- 1) (* x6 x3 x14 x5 x22)) (* (- 1) (* x6 x4 x15 x5 x22)) (* (- 1) (* x6 x23 x17 x4 x5)) (* (- 1) (* x6 x23 x3 x5 x16)) (* (- 1) (* x6 x3 x20 x7 x14)) (* (- 1) (* x6 x20 x7 x4 x15)) (* (- 1) (* x6 x17 x7 x4 x21)) (* (- 1) (* x6 x3 x7 x21 x16)) (* (- 1) (* x6 x3 x14 x8 x22)) (* (- 1) (* x6 x4 x8 x15 x22)) (* (- 1) (* x6 x23 x17 x4 x8)) (* (- 1) (* x6 x23 x3 x8 x16))) 0)) (and (>= (+ (* (- 1) x3) x18 (* x3 x20) (* x4 x21) (* (- 1) (* x3 x5)) (* (- 1) (* x6 x4)) (* (- 1) (* x18 x5 x5)) (* (- 1) (* x6 x5 x19)) (* (- 1) (* x6 x7 x18)) (* (- 1) (* x6 x8 x19)) (* (- 1) (* x20 x5 x5 x12)) (* (- 1) (* x13 x21 x5 x5)) (* (- 1) (* x6 x5 x22 x12)) (* (- 1) (* x6 x23 x13 x5)) (* (- 1) (* x6 x20 x7 x12)) (* (- 1) (* x6 x13 x7 x21)) (* (- 1) (* x6 x8 x22 x12)) (* (- 1) (* x6 x23 x13 x8)) (* (- 1) (* x3 x20 x14 x5 x5)) (* (- 1) (* x20 x4 x15 x5 x5)) (* (- 1) (* x17 x4 x21 x5 x5)) (* (- 1) (* x3 x21 x5 x5 x16)) (* (- 1) (* x6 x3 x14 x5 x22)) (* (- 1) (* x6 x4 x15 x5 x22)) (* (- 1) (* x6 x23 x17 x4 x5)) (* (- 1) (* x6 x23 x3 x5 x16)) (* (- 1) (* x6 x3 x20 x7 x14)) (* (- 1) (* x6 x20 x7 x4 x15)) (* (- 1) (* x6 x17 x7 x4 x21)) (* (- 1) (* x6 x3 x7 x21 x16)) (* (- 1) (* x6 x3 x14 x8 x22)) (* (- 1) (* x6 x4 x8 x15 x22)) (* (- 1) (* x6 x23 x17 x4 x8)) (* (- 1) (* x6 x23 x3 x8 x16))) 0) (>= (+ (* (- 1) x4) x19 (* x23 x4) (* x3 x22) (* (- 1) (* x3 x7)) (* (- 1) (* x4 x8)) (* (- 1) (* x7 x18 x5)) (* (- 1) (* x6 x7 x19)) (* (- 1) (* x7 x18 x8)) (* (- 1) (* x8 x8 x19)) (* (- 1) (* x20 x7 x5 x12)) (* (- 1) (* x13 x7 x21 x5)) (* (- 1) (* x6 x7 x22 x12)) (* (- 1) (* x6 x23 x13 x7)) (* (- 1) (* x20 x7 x8 x12)) (* (- 1) (* x13 x7 x21 x8)) (* (- 1) (* x8 x8 x22 x12)) (* (- 1) (* x23 x13 x8 x8)) (* (- 1) (* x3 x20 x7 x14 x5)) (* (- 1) (* x20 x7 x4 x15 x5)) (* (- 1) (* x17 x7 x4 x21 x5)) (* (- 1) (* x3 x7 x21 x5 x16)) (* (- 1) (* x6 x3 x7 x14 x22)) (* (- 1) (* x6 x7 x4 x15 x22)) (* (- 1) (* x6 x23 x17 x7 x4)) (* (- 1) (* x6 x23 x3 x7 x16)) (* (- 1) (* x3 x20 x7 x14 x8)) (* (- 1) (* x20 x7 x4 x8 x15)) (* (- 1) (* x17 x7 x4 x21 x8)) (* (- 1) (* x3 x7 x21 x8 x16)) (* (- 1) (* x3 x14 x8 x8 x22)) (* (- 1) (* x4 x8 x8 x15 x22)) (* (- 1) (* x23 x17 x4 x8 x8)) (* (- 1) (* x23 x3 x8 x8 x16))) 0))) (and (and (and (>= (+ (* x20 x5) (* x7 x21) (* (- 1) (* x20 x14 x5 x5 x5)) (* (- 1) (* x20 x7 x15 x5 x5)) (* (- 1) (* x17 x7 x21 x5 x5)) (* (- 1) (* x21 x5 x5 x5 x16)) (* (- 1) (* x6 x14 x5 x5 x22)) (* (- 1) (* x6 x7 x15 x5 x22)) (* (- 1) (* x6 x23 x17 x7 x5)) (* (- 1) (* x6 x23 x5 x5 x16)) (* (- 1) (* x6 x20 x7 x14 x5)) (* (- 1) (* x6 x20 x7 x7 x15)) (* (- 1) (* x6 x17 x7 x7 x21)) (* (- 1) (* x6 x7 x21 x5 x16)) (* (- 1) (* x6 x14 x8 x5 x22)) (* (- 1) (* x6 x7 x8 x15 x22)) (* (- 1) (* x6 x23 x17 x7 x8)) (* (- 1) (* x6 x23 x8 x5 x16))) 0) (>= (+ (* x21 x8) (* x6 x20) (* (- 1) (* x6 x20 x14 x5 x5)) (* (- 1) (* x20 x8 x15 x5 x5)) (* (- 1) (* x17 x21 x8 x5 x5)) (* (- 1) (* x6 x21 x5 x5 x16)) (* (- 1) (* x6 x6 x14 x5 x22)) (* (- 1) (* x6 x8 x15 x5 x22)) (* (- 1) (* x6 x23 x17 x8 x5)) (* (- 1) (* x6 x6 x23 x5 x16)) (* (- 1) (* x6 x6 x20 x7 x14)) (* (- 1) (* x6 x20 x7 x8 x15)) (* (- 1) (* x6 x17 x7 x21 x8)) (* (- 1) (* x6 x6 x7 x21 x16)) (* (- 1) (* x6 x6 x14 x8 x22)) (* (- 1) (* x6 x8 x8 x15 x22)) (* (- 1) (* x6 x23 x17 x8 x8)) (* (- 1) (* x6 x6 x23 x8 x16))) 0)) (>= (+ (* x23 x7) (* x5 x22) (* (- 1) (* x20 x7 x14 x5 x5)) (* (- 1) (* x20 x7 x7 x15 x5)) (* (- 1) (* x17 x7 x7 x21 x5)) (* (- 1) (* x7 x21 x5 x5 x16)) (* (- 1) (* x6 x7 x14 x5 x22)) (* (- 1) (* x6 x7 x7 x15 x22)) (* (- 1) (* x6 x23 x17 x7 x7)) (* (- 1) (* x6 x23 x7 x5 x16)) (* (- 1) (* x20 x7 x14 x8 x5)) (* (- 1) (* x20 x7 x7 x8 x15)) (* (- 1) (* x17 x7 x7 x21 x8)) (* (- 1) (* x7 x21 x8 x5 x16)) (* (- 1) (* x14 x8 x8 x5 x22)) (* (- 1) (* x7 x8 x8 x15 x22)) (* (- 1) (* x23 x17 x7 x8 x8)) (* (- 1) (* x23 x8 x8 x5 x16))) 0)) (>= (+ (* x23 x8) (* x6 x22) (* (- 1) (* x6 x20 x7 x14 x5)) (* (- 1) (* x6 x7 x21 x5 x16)) (* (- 1) (* x6 x7 x8 x15 x22)) (* (- 1) (* x6 x23 x17 x7 x8)) (* (- 1) (* x20 x7 x8 x15 x5)) (* (- 1) (* x17 x7 x21 x8 x5)) (* (- 1) (* x6 x6 x7 x14 x22)) (* (- 1) (* x6 x6 x23 x7 x16)) (* (- 1) (* x6 x20 x7 x14 x8)) (* (- 1) (* x20 x7 x8 x8 x15)) (* (- 1) (* x17 x7 x21 x8 x8)) (* (- 1) (* x6 x7 x21 x8 x16)) (* (- 1) (* x6 x14 x8 x8 x22)) (* (- 1) (* x8 x8 x8 x15 x22)) (* (- 1) (* x23 x17 x8 x8 x8)) (* (- 1) (* x6 x23 x8 x8 x16))) 0)))) (and (not (<= (+ (* (- 1) x24) x18 (* x20 x24) (* x21 x25)) 0)) (and (>= (+ (* (- 1) x24) x18 (* x20 x24) (* x21 x25)) 0) (>= (+ (* (- 1) x25) x19 (* x23 x25) (* x24 x22)) 0)))) (and (and (not (<= (+ x12 (* x3 x14) (* x4 x15)) 0)) (and (>= (+ x12 (* x3 x14) (* x4 x15)) 0) (>= (+ x13 (* x17 x4) (* x3 x16)) 0))) (and (and (and (>= (+ (* x14 x5) (* x7 x15)) 1) (>= (+ (* x6 x14) (* x8 x15)) 0)) (>= (+ (* x17 x7) (* x5 x16)) 0)) (>= (+ (* x17 x8) (* x6 x16)) 1)))) (and (and (and (not (<= (+ x0 (* (- 1) x9) (* x3 x1) (* x4 x2) (* (- 1) (* x3 x10)) (* (- 1) (* x4 x11))) 0)) (>= (+ x0 (* (- 1) x9) (* x3 x1) (* x4 x2) (* (- 1) (* x3 x10)) (* (- 1) (* x4 x11))) 0)) (and (>= (+ (* x1 x5) (* (- 1) (* x10 x5)) (* x7 x2) (* (- 1) (* x7 x11))) 0) (>= (+ (* (- 1) (* x11 x8)) (* x6 x1) (* x8 x2) (* (- 1) (* x6 x10))) 0))) (and (and (not (<= (+ (* x3 x1) (* x4 x2) (* (- 1) (* x1 x12)) (* (- 1) (* x13 x2)) (* (- 1) (* x3 x14 x1)) (* (- 1) (* x4 x1 x15)) (* (- 1) (* x17 x4 x2)) (* (- 1) (* x3 x2 x16))) 0)) (>= (+ (* x3 x1) (* x4 x2) (* (- 1) (* x1 x12)) (* (- 1) (* x13 x2)) (* (- 1) (* x3 x14 x1)) (* (- 1) (* x4 x1 x15)) (* (- 1) (* x17 x4 x2)) (* (- 1) (* x3 x2 x16))) 0)) (and (>= (+ (* x1 x5) (* x7 x2) (* (- 1) (* x14 x1 x5)) (* (- 1) (* x7 x1 x15)) (* (- 1) (* x17 x7 x2)) (* (- 1) (* x5 x2 x16))) 0) (>= (+ (* x6 x1) (* x8 x2) (* (- 1) (* x6 x14 x1)) (* (- 1) (* x1 x8 x15)) (* (- 1) (* x17 x8 x2)) (* (- 1) (* x6 x2 x16))) 0))))))
(exit)
(check-sat)
