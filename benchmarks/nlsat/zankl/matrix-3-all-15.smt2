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
(declare-fun x40 () Real)
(declare-fun x13 () Real)
(declare-fun x30 () Real)
(declare-fun x47 () Real)
(declare-fun x3 () Real)
(declare-fun x20 () Real)
(declare-fun x37 () Real)
(declare-fun x10 () Real)
(declare-fun x27 () Real)
(declare-fun x44 () Real)
(declare-fun x0 () Real)
(declare-fun x17 () Real)
(declare-fun x34 () Real)
(declare-fun x51 () Real)
(declare-fun x7 () Real)
(declare-fun x24 () Real)
(declare-fun x41 () Real)
(declare-fun x14 () Real)
(declare-fun x31 () Real)
(declare-fun x48 () Real)
(declare-fun x4 () Real)
(declare-fun x21 () Real)
(declare-fun x38 () Real)
(declare-fun x11 () Real)
(declare-fun x28 () Real)
(declare-fun x45 () Real)
(declare-fun x1 () Real)
(declare-fun x18 () Real)
(declare-fun x35 () Real)
(declare-fun x8 () Real)
(declare-fun x25 () Real)
(declare-fun x42 () Real)
(declare-fun x15 () Real)
(declare-fun x32 () Real)
(declare-fun x49 () Real)
(declare-fun x5 () Real)
(declare-fun x22 () Real)
(declare-fun x39 () Real)
(declare-fun x12 () Real)
(declare-fun x29 () Real)
(declare-fun x46 () Real)
(declare-fun x2 () Real)
(declare-fun x19 () Real)
(declare-fun x36 () Real)
(declare-fun x9 () Real)
(declare-fun x26 () Real)
(declare-fun x43 () Real)
(declare-fun x16 () Real)
(declare-fun x33 () Real)
(declare-fun x50 () Real)
(assert (>= x6 0))
(assert (>= x23 0))
(assert (>= x40 0))
(assert (>= x13 0))
(assert (>= x30 0))
(assert (>= x47 0))
(assert (>= x3 0))
(assert (>= x20 0))
(assert (>= x37 0))
(assert (>= x10 0))
(assert (>= x27 0))
(assert (>= x44 0))
(assert (>= x0 0))
(assert (>= x17 0))
(assert (>= x34 0))
(assert (>= x51 0))
(assert (>= x7 0))
(assert (>= x24 0))
(assert (>= x41 0))
(assert (>= x14 0))
(assert (>= x31 0))
(assert (>= x48 0))
(assert (>= x4 0))
(assert (>= x21 0))
(assert (>= x38 0))
(assert (>= x11 0))
(assert (>= x28 0))
(assert (>= x45 0))
(assert (>= x1 0))
(assert (>= x18 0))
(assert (>= x35 0))
(assert (>= x8 0))
(assert (>= x25 0))
(assert (>= x42 0))
(assert (>= x15 0))
(assert (>= x32 0))
(assert (>= x49 0))
(assert (>= x5 0))
(assert (>= x22 0))
(assert (>= x39 0))
(assert (>= x12 0))
(assert (>= x29 0))
(assert (>= x46 0))
(assert (>= x2 0))
(assert (>= x19 0))
(assert (>= x36 0))
(assert (>= x9 0))
(assert (>= x26 0))
(assert (>= x43 0))
(assert (>= x16 0))
(assert (>= x33 0))
(assert (>= x50 0))
(assert (let ((?v_6 (+ x0 (+ (+ (* x1 x4) (* x2 x5)) (* x3 x6))))) (let ((?v_0 (+ ?v_6 (+ (+ (* x25 x4) (* x26 x5)) (* x27 x6)))) (?v_13 (+ (+ (* x1 x16) (* x2 x19)) (* x3 x22))) (?v_14 (+ (+ (* x1 x17) (* x2 x20)) (* x3 x23))) (?v_15 (+ (+ (* x1 x18) (* x2 x21)) (* x3 x24)))) (let ((?v_8 (and (and (>= ?v_13 x1) (>= ?v_14 x2)) (>= ?v_15 x3))) (?v_1 (+ x0 (+ (+ (* x1 x28) (* x2 x29)) (* x3 x30)))) (?v_3 (+ (+ (* x1 x40) (* x2 x43)) (* x3 x46))) (?v_4 (+ (+ (* x1 x41) (* x2 x44)) (* x3 x47))) (?v_5 (+ (+ (* x1 x42) (* x2 x45)) (* x3 x48))) (?v_2 (+ x0 (+ (+ (* x25 x28) (* x26 x29)) (* x27 x30)))) (?v_19 (+ x28 (+ (+ (* x31 x4) (* x32 x5)) (* x33 x6)))) (?v_67 (+ (+ (* x40 x49) (* x41 x50)) (* x42 x51)))) (let ((?v_64 (+ ?v_19 ?v_67)) (?v_22 (+ x29 (+ (+ (* x34 x4) (* x35 x5)) (* x36 x6)))) (?v_70 (+ (+ (* x43 x49) (* x44 x50)) (* x45 x51)))) (let ((?v_65 (+ ?v_22 ?v_70)) (?v_24 (+ x30 (+ (+ (* x37 x4) (* x38 x5)) (* x39 x6)))) (?v_71 (+ (+ (* x46 x49) (* x47 x50)) (* x48 x51)))) (let ((?v_66 (+ ?v_24 ?v_71))) (let ((?v_7 (+ ?v_6 (+ (+ (* x25 ?v_64) (* x26 ?v_65)) (* x27 ?v_66)))) (?v_35 (+ (+ (* x31 x16) (* x32 x19)) (* x33 x22))) (?v_41 (+ (+ (* x34 x16) (* x35 x19)) (* x36 x22))) (?v_47 (+ (+ (* x37 x16) (* x38 x19)) (* x39 x22)))) (let ((?v_16 (+ (+ (* x25 ?v_35) (* x26 ?v_41)) (* x27 ?v_47))) (?v_37 (+ (+ (* x31 x17) (* x32 x20)) (* x33 x23))) (?v_43 (+ (+ (* x34 x17) (* x35 x20)) (* x36 x23))) (?v_49 (+ (+ (* x37 x17) (* x38 x20)) (* x39 x23)))) (let ((?v_17 (+ (+ (* x25 ?v_37) (* x26 ?v_43)) (* x27 ?v_49))) (?v_39 (+ (+ (* x31 x18) (* x32 x21)) (* x33 x24))) (?v_45 (+ (+ (* x34 x18) (* x35 x21)) (* x36 x24))) (?v_51 (+ (+ (* x37 x18) (* x38 x21)) (* x39 x24)))) (let ((?v_18 (+ (+ (* x25 ?v_39) (* x26 ?v_45)) (* x27 ?v_51))) (?v_20 (+ x4 (+ (+ (* x16 x28) (* x17 x29)) (* x18 x30)))) (?v_23 (+ x5 (+ (+ (* x19 x28) (* x20 x29)) (* x21 x30)))) (?v_25 (+ x6 (+ (+ (* x22 x28) (* x23 x29)) (* x24 x30))))) (let ((?v_9 (+ (+ x0 (+ (+ (* x1 ?v_20) (* x2 ?v_23)) (* x3 ?v_25))) (+ (+ (* x25 x49) (* x26 x50)) (* x27 x51)))) (?v_10 (+ (+ (* x1 x7) (* x2 x10)) (* x3 x13))) (?v_26 (+ (+ (* x31 x7) (* x32 x10)) (* x33 x13))) (?v_29 (+ (+ (* x34 x7) (* x35 x10)) (* x36 x13))) (?v_32 (+ (+ (* x37 x7) (* x38 x10)) (* x39 x13))) (?v_11 (+ (+ (* x1 x8) (* x2 x11)) (* x3 x14))) (?v_27 (+ (+ (* x31 x8) (* x32 x11)) (* x33 x14))) (?v_30 (+ (+ (* x34 x8) (* x35 x11)) (* x36 x14))) (?v_33 (+ (+ (* x37 x8) (* x38 x11)) (* x39 x14))) (?v_12 (+ (+ (* x1 x9) (* x2 x12)) (* x3 x15))) (?v_28 (+ (+ (* x31 x9) (* x32 x12)) (* x33 x15))) (?v_31 (+ (+ (* x34 x9) (* x35 x12)) (* x36 x15))) (?v_34 (+ (+ (* x37 x9) (* x38 x12)) (* x39 x15))) (?v_36 (+ (+ (* x16 x31) (* x17 x34)) (* x18 x37))) (?v_42 (+ (+ (* x19 x31) (* x20 x34)) (* x21 x37))) (?v_48 (+ (+ (* x22 x31) (* x23 x34)) (* x24 x37))) (?v_38 (+ (+ (* x16 x32) (* x17 x35)) (* x18 x38))) (?v_44 (+ (+ (* x19 x32) (* x20 x35)) (* x21 x38))) (?v_50 (+ (+ (* x22 x32) (* x23 x35)) (* x24 x38))) (?v_40 (+ (+ (* x16 x33) (* x17 x36)) (* x18 x39))) (?v_46 (+ (+ (* x19 x33) (* x20 x36)) (* x21 x39))) (?v_52 (+ (+ (* x22 x33) (* x23 x36)) (* x24 x39))) (?v_53 (+ (+ (* x16 x40) (* x17 x43)) (* x18 x46))) (?v_56 (+ (+ (* x19 x40) (* x20 x43)) (* x21 x46))) (?v_59 (+ (+ (* x22 x40) (* x23 x43)) (* x24 x46))) (?v_54 (+ (+ (* x16 x41) (* x17 x44)) (* x18 x47))) (?v_57 (+ (+ (* x19 x41) (* x20 x44)) (* x21 x47))) (?v_60 (+ (+ (* x22 x41) (* x23 x44)) (* x24 x47))) (?v_55 (+ (+ (* x16 x42) (* x17 x45)) (* x18 x48))) (?v_58 (+ (+ (* x19 x42) (* x20 x45)) (* x21 x48))) (?v_61 (+ (+ (* x22 x42) (* x23 x45)) (* x24 x48)))) (let ((?v_72 (and (and (and (and (and (and (and (> ?v_0 x0) (>= ?v_0 x0)) ?v_8) (and (and (>= (+ (+ (* x25 x16) (* x26 x19)) (* x27 x22)) x25) (>= (+ (+ (* x25 x17) (* x26 x20)) (* x27 x23)) x26)) (>= (+ (+ (* x25 x18) (* x26 x21)) (* x27 x24)) x27))) (and (and (> ?v_1 x0) (>= ?v_1 x0)) (and (and (>= ?v_3 x1) (>= ?v_4 x2)) (>= ?v_5 x3)))) (and (and (and (and (> ?v_1 ?v_2) (>= ?v_1 ?v_2)) (and (and (>= (+ (+ (* x1 x31) (* x2 x34)) (* x3 x37)) x1) (>= (+ (+ (* x1 x32) (* x2 x35)) (* x3 x38)) x2)) (>= (+ (+ (* x1 x33) (* x2 x36)) (* x3 x39)) x3))) (and (and (>= ?v_3 (+ (+ (* x25 x31) (* x26 x34)) (* x27 x37))) (>= ?v_4 (+ (+ (* x25 x32) (* x26 x35)) (* x27 x38)))) (>= ?v_5 (+ (+ (* x25 x33) (* x26 x36)) (* x27 x39))))) (and (and (>= x25 (+ (+ (* x25 x40) (* x26 x43)) (* x27 x46))) (>= x26 (+ (+ (* x25 x41) (* x26 x44)) (* x27 x47)))) (>= x27 (+ (+ (* x25 x42) (* x26 x45)) (* x27 x48)))))) (and (and (and (> ?v_7 x0) (>= ?v_7 x0)) ?v_8) (and (and (>= ?v_16 x25) (>= ?v_17 x26)) (>= ?v_18 x27)))) (and (and (and (and (> ?v_7 ?v_9) (>= ?v_7 ?v_9)) (and (and (>= (+ ?v_10 (+ (+ (* x25 ?v_26) (* x26 ?v_29)) (* x27 ?v_32))) ?v_10) (>= (+ ?v_11 (+ (+ (* x25 ?v_27) (* x26 ?v_30)) (* x27 ?v_33))) ?v_11)) (>= (+ ?v_12 (+ (+ (* x25 ?v_28) (* x26 ?v_31)) (* x27 ?v_34))) ?v_12))) (and (and (>= ?v_13 (+ (+ (* x1 ?v_36) (* x2 ?v_42)) (* x3 ?v_48))) (>= ?v_14 (+ (+ (* x1 ?v_38) (* x2 ?v_44)) (* x3 ?v_50)))) (>= ?v_15 (+ (+ (* x1 ?v_40) (* x2 ?v_46)) (* x3 ?v_52))))) (and (and (>= ?v_16 (+ (+ (* x1 ?v_53) (* x2 ?v_56)) (* x3 ?v_59))) (>= ?v_17 (+ (+ (* x1 ?v_54) (* x2 ?v_57)) (* x3 ?v_60)))) (>= ?v_18 (+ (+ (* x1 ?v_55) (* x2 ?v_58)) (* x3 ?v_61))))))) (?v_21 (+ ?v_19 (+ (+ (* x40 x4) (* x41 x5)) (* x42 x6)))) (?v_63 (+ x28 (+ (+ (* x40 x28) (* x41 x29)) (* x42 x30)))) (?v_62 (+ x28 (+ (+ (* x31 x28) (* x32 x29)) (* x33 x30)))) (?v_69 (+ (+ x28 (+ (+ (* x31 ?v_20) (* x32 ?v_23)) (* x33 ?v_25))) ?v_67)) (?v_68 (+ ?v_19 (+ (+ (* x40 ?v_64) (* x41 ?v_65)) (* x42 ?v_66))))) (and (and (and (and ?v_72 (and (and (and (and (> ?v_21 ?v_20) (and (and (>= ?v_21 ?v_20) (>= (+ ?v_22 (+ (+ (* x43 x4) (* x44 x5)) (* x45 x6))) ?v_23)) (>= (+ ?v_24 (+ (+ (* x46 x4) (* x47 x5)) (* x48 x6))) ?v_25))) (and (and (and (and (and (and (and (and (>= (+ ?v_26 (+ (+ (* x40 x7) (* x41 x10)) (* x42 x13))) x7) (>= (+ ?v_27 (+ (+ (* x40 x8) (* x41 x11)) (* x42 x14))) x8)) (>= (+ ?v_28 (+ (+ (* x40 x9) (* x41 x12)) (* x42 x15))) x9)) (>= (+ ?v_29 (+ (+ (* x43 x7) (* x44 x10)) (* x45 x13))) x10)) (>= (+ ?v_30 (+ (+ (* x43 x8) (* x44 x11)) (* x45 x14))) x11)) (>= (+ ?v_31 (+ (+ (* x43 x9) (* x44 x12)) (* x45 x15))) x12)) (>= (+ ?v_32 (+ (+ (* x46 x7) (* x47 x10)) (* x48 x13))) x13)) (>= (+ ?v_33 (+ (+ (* x46 x8) (* x47 x11)) (* x48 x14))) x14)) (>= (+ ?v_34 (+ (+ (* x46 x9) (* x47 x12)) (* x48 x15))) x15))) (and (and (and (and (and (and (and (and (>= ?v_35 ?v_36) (>= ?v_37 ?v_38)) (>= ?v_39 ?v_40)) (>= ?v_41 ?v_42)) (>= ?v_43 ?v_44)) (>= ?v_45 ?v_46)) (>= ?v_47 ?v_48)) (>= ?v_49 ?v_50)) (>= ?v_51 ?v_52))) (and (and (and (and (and (and (and (and (>= (+ (+ (* x40 x16) (* x41 x19)) (* x42 x22)) ?v_53) (>= (+ (+ (* x40 x17) (* x41 x20)) (* x42 x23)) ?v_54)) (>= (+ (+ (* x40 x18) (* x41 x21)) (* x42 x24)) ?v_55)) (>= (+ (+ (* x43 x16) (* x44 x19)) (* x45 x22)) ?v_56)) (>= (+ (+ (* x43 x17) (* x44 x20)) (* x45 x23)) ?v_57)) (>= (+ (+ (* x43 x18) (* x44 x21)) (* x45 x24)) ?v_58)) (>= (+ (+ (* x46 x16) (* x47 x19)) (* x48 x22)) ?v_59)) (>= (+ (+ (* x46 x17) (* x47 x20)) (* x48 x23)) ?v_60)) (>= (+ (+ (* x46 x18) (* x47 x21)) (* x48 x24)) ?v_61)))) (and (and (and (and (> ?v_62 ?v_63) (and (and (>= ?v_62 ?v_63) (>= (+ x29 (+ (+ (* x34 x28) (* x35 x29)) (* x36 x30))) (+ x29 (+ (+ (* x43 x28) (* x44 x29)) (* x45 x30))))) (>= (+ x30 (+ (+ (* x37 x28) (* x38 x29)) (* x39 x30))) (+ x30 (+ (+ (* x46 x28) (* x47 x29)) (* x48 x30)))))) (and (and (and (and (and (and (and (and (>= (+ (+ (* x31 x31) (* x32 x34)) (* x33 x37)) x31) (>= (+ (+ (* x31 x32) (* x32 x35)) (* x33 x38)) x32)) (>= (+ (+ (* x31 x33) (* x32 x36)) (* x33 x39)) x33)) (>= (+ (+ (* x34 x31) (* x35 x34)) (* x36 x37)) x34)) (>= (+ (+ (* x34 x32) (* x35 x35)) (* x36 x38)) x35)) (>= (+ (+ (* x34 x33) (* x35 x36)) (* x36 x39)) x36)) (>= (+ (+ (* x37 x31) (* x38 x34)) (* x39 x37)) x37)) (>= (+ (+ (* x37 x32) (* x38 x35)) (* x39 x38)) x38)) (>= (+ (+ (* x37 x33) (* x38 x36)) (* x39 x39)) x39))) (and (and (and (and (and (and (and (and (>= (+ (+ (* x31 x40) (* x32 x43)) (* x33 x46)) (+ (+ (* x40 x31) (* x41 x34)) (* x42 x37))) (>= (+ (+ (* x31 x41) (* x32 x44)) (* x33 x47)) (+ (+ (* x40 x32) (* x41 x35)) (* x42 x38)))) (>= (+ (+ (* x31 x42) (* x32 x45)) (* x33 x48)) (+ (+ (* x40 x33) (* x41 x36)) (* x42 x39)))) (>= (+ (+ (* x34 x40) (* x35 x43)) (* x36 x46)) (+ (+ (* x43 x31) (* x44 x34)) (* x45 x37)))) (>= (+ (+ (* x34 x41) (* x35 x44)) (* x36 x47)) (+ (+ (* x43 x32) (* x44 x35)) (* x45 x38)))) (>= (+ (+ (* x34 x42) (* x35 x45)) (* x36 x48)) (+ (+ (* x43 x33) (* x44 x36)) (* x45 x39)))) (>= (+ (+ (* x37 x40) (* x38 x43)) (* x39 x46)) (+ (+ (* x46 x31) (* x47 x34)) (* x48 x37)))) (>= (+ (+ (* x37 x41) (* x38 x44)) (* x39 x47)) (+ (+ (* x46 x32) (* x47 x35)) (* x48 x38)))) (>= (+ (+ (* x37 x42) (* x38 x45)) (* x39 x48)) (+ (+ (* x46 x33) (* x47 x36)) (* x48 x39))))) (and (and (and (and (and (and (and (and (>= x40 (+ (+ (* x40 x40) (* x41 x43)) (* x42 x46))) (>= x41 (+ (+ (* x40 x41) (* x41 x44)) (* x42 x47)))) (>= x42 (+ (+ (* x40 x42) (* x41 x45)) (* x42 x48)))) (>= x43 (+ (+ (* x43 x40) (* x44 x43)) (* x45 x46)))) (>= x44 (+ (+ (* x43 x41) (* x44 x44)) (* x45 x47)))) (>= x45 (+ (+ (* x43 x42) (* x44 x45)) (* x45 x48)))) (>= x46 (+ (+ (* x46 x40) (* x47 x43)) (* x48 x46)))) (>= x47 (+ (+ (* x46 x41) (* x47 x44)) (* x48 x47)))) (>= x48 (+ (+ (* x46 x42) (* x47 x45)) (* x48 x48)))))) (and (and (and (and (> ?v_68 ?v_69) (and (and (>= ?v_68 ?v_69) (>= (+ ?v_22 (+ (+ (* x43 ?v_64) (* x44 ?v_65)) (* x45 ?v_66))) (+ (+ x29 (+ (+ (* x34 ?v_20) (* x35 ?v_23)) (* x36 ?v_25))) ?v_70))) (>= (+ ?v_24 (+ (+ (* x46 ?v_64) (* x47 ?v_65)) (* x48 ?v_66))) (+ (+ x30 (+ (+ (* x37 ?v_20) (* x38 ?v_23)) (* x39 ?v_25))) ?v_71)))) (and (and (and (and (and (and (and (and (>= (+ ?v_26 (+ (+ (* x40 ?v_26) (* x41 ?v_29)) (* x42 ?v_32))) ?v_26) (>= (+ ?v_27 (+ (+ (* x40 ?v_27) (* x41 ?v_30)) (* x42 ?v_33))) ?v_27)) (>= (+ ?v_28 (+ (+ (* x40 ?v_28) (* x41 ?v_31)) (* x42 ?v_34))) ?v_28)) (>= (+ ?v_29 (+ (+ (* x43 ?v_26) (* x44 ?v_29)) (* x45 ?v_32))) ?v_29)) (>= (+ ?v_30 (+ (+ (* x43 ?v_27) (* x44 ?v_30)) (* x45 ?v_33))) ?v_30)) (>= (+ ?v_31 (+ (+ (* x43 ?v_28) (* x44 ?v_31)) (* x45 ?v_34))) ?v_31)) (>= (+ ?v_32 (+ (+ (* x46 ?v_26) (* x47 ?v_29)) (* x48 ?v_32))) ?v_32)) (>= (+ ?v_33 (+ (+ (* x46 ?v_27) (* x47 ?v_30)) (* x48 ?v_33))) ?v_33)) (>= (+ ?v_34 (+ (+ (* x46 ?v_28) (* x47 ?v_31)) (* x48 ?v_34))) ?v_34))) (and (and (and (and (and (and (and (and (>= ?v_35 (+ (+ (* x31 ?v_36) (* x32 ?v_42)) (* x33 ?v_48))) (>= ?v_37 (+ (+ (* x31 ?v_38) (* x32 ?v_44)) (* x33 ?v_50)))) (>= ?v_39 (+ (+ (* x31 ?v_40) (* x32 ?v_46)) (* x33 ?v_52)))) (>= ?v_41 (+ (+ (* x34 ?v_36) (* x35 ?v_42)) (* x36 ?v_48)))) (>= ?v_43 (+ (+ (* x34 ?v_38) (* x35 ?v_44)) (* x36 ?v_50)))) (>= ?v_45 (+ (+ (* x34 ?v_40) (* x35 ?v_46)) (* x36 ?v_52)))) (>= ?v_47 (+ (+ (* x37 ?v_36) (* x38 ?v_42)) (* x39 ?v_48)))) (>= ?v_49 (+ (+ (* x37 ?v_38) (* x38 ?v_44)) (* x39 ?v_50)))) (>= ?v_51 (+ (+ (* x37 ?v_40) (* x38 ?v_46)) (* x39 ?v_52))))) (and (and (and (and (and (and (and (and (>= (+ (+ (* x40 ?v_35) (* x41 ?v_41)) (* x42 ?v_47)) (+ (+ (* x31 ?v_53) (* x32 ?v_56)) (* x33 ?v_59))) (>= (+ (+ (* x40 ?v_37) (* x41 ?v_43)) (* x42 ?v_49)) (+ (+ (* x31 ?v_54) (* x32 ?v_57)) (* x33 ?v_60)))) (>= (+ (+ (* x40 ?v_39) (* x41 ?v_45)) (* x42 ?v_51)) (+ (+ (* x31 ?v_55) (* x32 ?v_58)) (* x33 ?v_61)))) (>= (+ (+ (* x43 ?v_35) (* x44 ?v_41)) (* x45 ?v_47)) (+ (+ (* x34 ?v_53) (* x35 ?v_56)) (* x36 ?v_59)))) (>= (+ (+ (* x43 ?v_37) (* x44 ?v_43)) (* x45 ?v_49)) (+ (+ (* x34 ?v_54) (* x35 ?v_57)) (* x36 ?v_60)))) (>= (+ (+ (* x43 ?v_39) (* x44 ?v_45)) (* x45 ?v_51)) (+ (+ (* x34 ?v_55) (* x35 ?v_58)) (* x36 ?v_61)))) (>= (+ (+ (* x46 ?v_35) (* x47 ?v_41)) (* x48 ?v_47)) (+ (+ (* x37 ?v_53) (* x38 ?v_56)) (* x39 ?v_59)))) (>= (+ (+ (* x46 ?v_37) (* x47 ?v_43)) (* x48 ?v_49)) (+ (+ (* x37 ?v_54) (* x38 ?v_57)) (* x39 ?v_60)))) (>= (+ (+ (* x46 ?v_39) (* x47 ?v_45)) (* x48 ?v_51)) (+ (+ (* x37 ?v_55) (* x38 ?v_58)) (* x39 ?v_61)))))) ?v_72))))))))))))))
(check-sat)
(exit)
