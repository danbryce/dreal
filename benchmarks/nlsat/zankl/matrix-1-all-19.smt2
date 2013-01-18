(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x6 () Real)
(declare-fun x23 () Real)
(declare-fun x13 () Real)
(declare-fun x30 () Real)
(declare-fun x3 () Real)
(declare-fun x20 () Real)
(declare-fun x10 () Real)
(declare-fun x27 () Real)
(declare-fun x0 () Real)
(declare-fun x17 () Real)
(declare-fun x34 () Real)
(declare-fun x7 () Real)
(declare-fun x24 () Real)
(declare-fun x14 () Real)
(declare-fun x31 () Real)
(declare-fun x4 () Real)
(declare-fun x21 () Real)
(declare-fun x11 () Real)
(declare-fun x28 () Real)
(declare-fun x1 () Real)
(declare-fun x18 () Real)
(declare-fun x8 () Real)
(declare-fun x25 () Real)
(declare-fun x15 () Real)
(declare-fun x32 () Real)
(declare-fun x5 () Real)
(declare-fun x22 () Real)
(declare-fun x12 () Real)
(declare-fun x29 () Real)
(declare-fun x2 () Real)
(declare-fun x19 () Real)
(declare-fun x9 () Real)
(declare-fun x26 () Real)
(declare-fun x16 () Real)
(declare-fun x33 () Real)
(assert (>= x6 0))
(assert (>= x23 0))
(assert (>= x13 0))
(assert (>= x30 0))
(assert (>= x3 0))
(assert (>= x20 0))
(assert (>= x10 0))
(assert (>= x27 0))
(assert (>= x0 0))
(assert (>= x17 0))
(assert (>= x34 0))
(assert (>= x7 0))
(assert (>= x24 0))
(assert (>= x14 0))
(assert (>= x31 0))
(assert (>= x4 0))
(assert (>= x21 0))
(assert (>= x11 0))
(assert (>= x28 0))
(assert (>= x1 0))
(assert (>= x18 0))
(assert (>= x8 0))
(assert (>= x25 0))
(assert (>= x15 0))
(assert (>= x32 0))
(assert (>= x5 0))
(assert (>= x22 0))
(assert (>= x12 0))
(assert (>= x29 0))
(assert (>= x2 0))
(assert (>= x19 0))
(assert (>= x9 0))
(assert (>= x26 0))
(assert (>= x16 0))
(assert (>= x33 0))
(assert (let ((?v_0 (+ x0 (* x2 x3))) (?v_2 (* x2 x4)) (?v_1 (+ x5 (* x6 x7))) (?v_3 (+ (+ x10 (* x11 x3)) (* x12 x3))) (?v_13 (* x15 x3))) (let ((?v_4 (+ (+ x13 (* x14 x3)) ?v_13)) (?v_6 (* x14 x4)) (?v_7 (* x15 x4)) (?v_8 (* x21 x3)) (?v_9 (* x22 x3))) (let ((?v_5 (+ (+ (+ x16 (* x17 x18)) ?v_8) ?v_9)) (?v_11 (* x21 x4)) (?v_12 (* x22 x4)) (?v_10 (+ (+ (+ x16 (* x17 x23)) ?v_8) ?v_9)) (?v_14 (+ (+ x13 (* x14 x7)) ?v_13)) (?v_17 (* x14 x8)) (?v_16 (+ (* x14 x9) ?v_7)) (?v_15 (+ (+ (+ x16 (* x17 x24)) ?v_8) ?v_9))) (let ((?v_43 (and (and (and (and (and (and (and (and (and (and (> ?v_0 x0) (>= ?v_0 x0)) (>= ?v_2 x2)) (and (and (and (> ?v_0 ?v_1) (>= ?v_0 ?v_1)) (>= x1 (* x6 x8))) (>= ?v_2 (* x6 x9)))) (and (and (and (> ?v_3 x10) (>= ?v_3 x10)) (>= (* x11 x4) x11)) (>= (* x12 x4) x12))) (and (and (and (> ?v_4 x10) (>= ?v_4 x10)) (>= ?v_6 x12)) (>= ?v_7 x11))) (and (and (and (> ?v_4 ?v_5) (>= ?v_4 ?v_5)) (>= ?v_6 (+ (* x17 x20) ?v_11))) (>= ?v_7 (+ (* x17 x19) ?v_12)))) (and (and (and (> ?v_10 x0) (>= ?v_10 x0)) (>= ?v_11 x1)) (>= ?v_12 x2))) (and (and (and (> ?v_10 ?v_14) (>= ?v_10 ?v_14)) (>= ?v_11 ?v_17)) (>= ?v_12 ?v_16))) (and (and (and (> ?v_15 x0) (>= ?v_15 x0)) (>= ?v_11 x2)) (>= ?v_12 x1))) (and (and (and (> ?v_15 ?v_14) (>= ?v_15 ?v_14)) (>= ?v_11 ?v_16)) (>= ?v_12 ?v_17)))) (?v_19 (+ x25 (* x26 x7))) (?v_18 (+ x7 (* x9 x3))) (?v_20 (+ x7 (* x9 x27))) (?v_21 (+ x25 (* x26 x3))) (?v_23 (+ x18 (* x19 x3)))) (let ((?v_22 (+ ?v_23 (* x20 x3))) (?v_24 (+ ?v_23 (* x20 x27))) (?v_25 (+ x18 (* x19 x27))) (?v_26 (+ x28 (* x29 x27))) (?v_28 (+ x28 (* x29 x3)))) (let ((?v_27 (+ ?v_28 (* x30 x27))) (?v_31 (* x29 x4)) (?v_32 (* x33 x3)) (?v_33 (* x34 x3))) (let ((?v_30 (+ (+ (+ x31 (* x32 x18)) ?v_32) ?v_33)) (?v_34 (* x30 x3))) (let ((?v_29 (+ ?v_28 ?v_34)) (?v_37 (* x33 x4)) (?v_38 (* x34 x4)) (?v_39 (* x30 x4)) (?v_36 (+ (+ x28 (* x29 x7)) ?v_34)) (?v_35 (+ (+ (+ x31 (* x32 x23)) ?v_32) ?v_33)) (?v_42 (* x29 x8))) (let ((?v_41 (+ (* x29 x9) ?v_39)) (?v_40 (+ (+ (+ x31 (* x32 x24)) ?v_32) ?v_33))) (and (and (and (and (and (and (and (and (and (and (and (and ?v_43 (and (and (and (> ?v_18 ?v_19) (>= ?v_18 ?v_19)) (>= x8 (* x26 x8))) (>= (* x9 x4) (* x26 x9)))) (and (and (> ?v_20 0) (>= ?v_20 0)) (>= x8 1))) (and (and (> ?v_21 0) (>= ?v_21 0)) (>= (* x26 x4) 1))) (and (and (and (> ?v_22 x18) (>= ?v_22 x18)) (>= (* x19 x4) x19)) (>= (* x20 x4) x20))) (and (> ?v_24 x24) (>= ?v_24 x24))) (and (> ?v_25 x23) (>= ?v_25 x23))) (and (> ?v_26 x27) (>= ?v_26 x27))) (and (and (> ?v_27 x3) (>= ?v_27 x3)) (>= ?v_31 x4))) (and (and (and (> ?v_29 ?v_30) (>= ?v_29 ?v_30)) (>= ?v_31 (+ (* x32 x20) ?v_37))) (>= ?v_39 (+ (* x32 x19) ?v_38)))) (and (and (and (> ?v_35 ?v_36) (>= ?v_35 ?v_36)) (>= ?v_37 ?v_42)) (>= ?v_38 ?v_41))) (and (and (and (> ?v_40 ?v_36) (>= ?v_40 ?v_36)) (>= ?v_37 ?v_41)) (>= ?v_38 ?v_42))) ?v_43)))))))))))
(check-sat)
(exit)
