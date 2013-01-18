(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x6 () Real)
(declare-fun x84 () Real)
(declare-fun x23 () Real)
(declare-fun x40 () Real)
(declare-fun x57 () Real)
(declare-fun x74 () Real)
(declare-fun x13 () Real)
(declare-fun x91 () Real)
(declare-fun x30 () Real)
(declare-fun x47 () Real)
(declare-fun x64 () Real)
(declare-fun x3 () Real)
(declare-fun x81 () Real)
(declare-fun x20 () Real)
(declare-fun x37 () Real)
(declare-fun x54 () Real)
(declare-fun x71 () Real)
(declare-fun x10 () Real)
(declare-fun x88 () Real)
(declare-fun x27 () Real)
(declare-fun x44 () Real)
(declare-fun x61 () Real)
(declare-fun x0 () Real)
(declare-fun x78 () Real)
(declare-fun x17 () Real)
(declare-fun x34 () Real)
(declare-fun x51 () Real)
(declare-fun x68 () Real)
(declare-fun x7 () Real)
(declare-fun x85 () Real)
(declare-fun x24 () Real)
(declare-fun x41 () Real)
(declare-fun x58 () Real)
(declare-fun x75 () Real)
(declare-fun x14 () Real)
(declare-fun x92 () Real)
(declare-fun x31 () Real)
(declare-fun x48 () Real)
(declare-fun x65 () Real)
(declare-fun x4 () Real)
(declare-fun x82 () Real)
(declare-fun x21 () Real)
(declare-fun x38 () Real)
(declare-fun x55 () Real)
(declare-fun x72 () Real)
(declare-fun x11 () Real)
(declare-fun x89 () Real)
(declare-fun x28 () Real)
(declare-fun x45 () Real)
(declare-fun x62 () Real)
(declare-fun x1 () Real)
(declare-fun x79 () Real)
(declare-fun x18 () Real)
(declare-fun x35 () Real)
(declare-fun x52 () Real)
(declare-fun x69 () Real)
(declare-fun x8 () Real)
(declare-fun x86 () Real)
(declare-fun x25 () Real)
(declare-fun x42 () Real)
(declare-fun x59 () Real)
(declare-fun x76 () Real)
(declare-fun x15 () Real)
(declare-fun x93 () Real)
(declare-fun x32 () Real)
(declare-fun x49 () Real)
(declare-fun x66 () Real)
(declare-fun x5 () Real)
(declare-fun x83 () Real)
(declare-fun x22 () Real)
(declare-fun x39 () Real)
(declare-fun x56 () Real)
(declare-fun x73 () Real)
(declare-fun x12 () Real)
(declare-fun x90 () Real)
(declare-fun x29 () Real)
(declare-fun x46 () Real)
(declare-fun x63 () Real)
(declare-fun x2 () Real)
(declare-fun x80 () Real)
(declare-fun x19 () Real)
(declare-fun x36 () Real)
(declare-fun x53 () Real)
(declare-fun x70 () Real)
(declare-fun x9 () Real)
(declare-fun x87 () Real)
(declare-fun x26 () Real)
(declare-fun x43 () Real)
(declare-fun x60 () Real)
(declare-fun x77 () Real)
(declare-fun x16 () Real)
(declare-fun x33 () Real)
(declare-fun x50 () Real)
(declare-fun x67 () Real)
(assert (>= x6 0))
(assert (>= x84 0))
(assert (>= x23 0))
(assert (>= x40 0))
(assert (>= x57 0))
(assert (>= x74 0))
(assert (>= x13 0))
(assert (>= x91 0))
(assert (>= x30 0))
(assert (>= x47 0))
(assert (>= x64 0))
(assert (>= x3 0))
(assert (>= x81 0))
(assert (>= x20 0))
(assert (>= x37 0))
(assert (>= x54 0))
(assert (>= x71 0))
(assert (>= x10 0))
(assert (>= x88 0))
(assert (>= x27 0))
(assert (>= x44 0))
(assert (>= x61 0))
(assert (>= x0 0))
(assert (>= x78 0))
(assert (>= x17 0))
(assert (>= x34 0))
(assert (>= x51 0))
(assert (>= x68 0))
(assert (>= x7 0))
(assert (>= x85 0))
(assert (>= x24 0))
(assert (>= x41 0))
(assert (>= x58 0))
(assert (>= x75 0))
(assert (>= x14 0))
(assert (>= x92 0))
(assert (>= x31 0))
(assert (>= x48 0))
(assert (>= x65 0))
(assert (>= x4 0))
(assert (>= x82 0))
(assert (>= x21 0))
(assert (>= x38 0))
(assert (>= x55 0))
(assert (>= x72 0))
(assert (>= x11 0))
(assert (>= x89 0))
(assert (>= x28 0))
(assert (>= x45 0))
(assert (>= x62 0))
(assert (>= x1 0))
(assert (>= x79 0))
(assert (>= x18 0))
(assert (>= x35 0))
(assert (>= x52 0))
(assert (>= x69 0))
(assert (>= x8 0))
(assert (>= x86 0))
(assert (>= x25 0))
(assert (>= x42 0))
(assert (>= x59 0))
(assert (>= x76 0))
(assert (>= x15 0))
(assert (>= x93 0))
(assert (>= x32 0))
(assert (>= x49 0))
(assert (>= x66 0))
(assert (>= x5 0))
(assert (>= x83 0))
(assert (>= x22 0))
(assert (>= x39 0))
(assert (>= x56 0))
(assert (>= x73 0))
(assert (>= x12 0))
(assert (>= x90 0))
(assert (>= x29 0))
(assert (>= x46 0))
(assert (>= x63 0))
(assert (>= x2 0))
(assert (>= x80 0))
(assert (>= x19 0))
(assert (>= x36 0))
(assert (>= x53 0))
(assert (>= x70 0))
(assert (>= x9 0))
(assert (>= x87 0))
(assert (>= x26 0))
(assert (>= x43 0))
(assert (>= x60 0))
(assert (>= x77 0))
(assert (>= x16 0))
(assert (>= x33 0))
(assert (>= x50 0))
(assert (>= x67 0))
(assert (and (and (and (and (and (and (not (<= (+ (* (- 1) (* x1 x5)) (* (- 1) (* x3 x7)) (* (- 1) (* x4 x8)) (* (- 1) (* x6 x2))) 0)) (>= (+ (* (- 1) (* x1 x5)) (* (- 1) (* x3 x7)) (* (- 1) (* x4 x8)) (* (- 1) (* x6 x2))) 0)) (and (and (and (>= (+ x1 (* (- 1) (* x1 x9)) (* (- 1) (* x3 x17)) (* (- 1) (* x4 x21)) (* (- 1) (* x13 x2))) 0) (>= (+ x2 (* (- 1) (* x3 x18)) (* (- 1) (* x4 x22)) (* (- 1) (* x10 x1)) (* (- 1) (* x14 x2))) 0)) (>= (+ x3 (* (- 1) (* x3 x19)) (* (- 1) (* x11 x1)) (* (- 1) (* x15 x2)) (* (- 1) (* x23 x4))) 0)) (>= (+ x4 (* (- 1) (* x1 x12)) (* (- 1) (* x2 x16)) (* (- 1) (* x3 x20)) (* (- 1) (* x24 x4))) 0))) (and (and (not (<= (+ x0 (* (- 1) x25) (* (- 1) (* x30 x34)) (* (- 1) (* x31 x35)) (* (- 1) (* x32 x36)) (* (- 1) (* x37 x33)) (* (- 1) (* x30 x38 x5)) (* (- 1) (* x40 x30 x7)) (* (- 1) (* x30 x41 x8)) (* (- 1) (* x6 x30 x39)) (* (- 1) (* x31 x42 x5)) (* (- 1) (* x44 x7 x31)) (* (- 1) (* x31 x45 x8)) (* (- 1) (* x6 x31 x43)) (* (- 1) (* x32 x5 x46)) (* (- 1) (* x6 x47 x32)) (* (- 1) (* x7 x48 x32)) (* (- 1) (* x8 x32 x49)) (* (- 1) (* x5 x33 x50)) (* (- 1) (* x6 x51 x33)) (* (- 1) (* x7 x52 x33)) (* (- 1) (* x8 x53 x33))) 0)) (>= (+ x0 (* (- 1) x25) (* (- 1) (* x30 x34)) (* (- 1) (* x31 x35)) (* (- 1) (* x32 x36)) (* (- 1) (* x37 x33)) (* (- 1) (* x30 x38 x5)) (* (- 1) (* x40 x30 x7)) (* (- 1) (* x30 x41 x8)) (* (- 1) (* x6 x30 x39)) (* (- 1) (* x31 x42 x5)) (* (- 1) (* x44 x7 x31)) (* (- 1) (* x31 x45 x8)) (* (- 1) (* x6 x31 x43)) (* (- 1) (* x32 x5 x46)) (* (- 1) (* x6 x47 x32)) (* (- 1) (* x7 x48 x32)) (* (- 1) (* x8 x32 x49)) (* (- 1) (* x5 x33 x50)) (* (- 1) (* x6 x51 x33)) (* (- 1) (* x7 x52 x33)) (* (- 1) (* x8 x53 x33))) 0)) (and (and (and (>= (+ x1 (* (- 1) x26) (* (- 1) (* x30 x38 x9)) (* (- 1) (* x40 x30 x17)) (* (- 1) (* x30 x41 x21)) (* (- 1) (* x13 x30 x39)) (* (- 1) (* x31 x42 x9)) (* (- 1) (* x44 x17 x31)) (* (- 1) (* x13 x31 x43)) (* (- 1) (* x31 x21 x45)) (* (- 1) (* x32 x46 x9)) (* (- 1) (* x13 x47 x32)) (* (- 1) (* x17 x48 x32)) (* (- 1) (* x21 x32 x49)) (* (- 1) (* x9 x33 x50)) (* (- 1) (* x13 x51 x33)) (* (- 1) (* x17 x52 x33)) (* (- 1) (* x21 x53 x33))) 0) (>= (+ (* (- 1) x27) x2 (* (- 1) (* x40 x30 x18)) (* (- 1) (* x30 x41 x22)) (* (- 1) (* x30 x10 x38)) (* (- 1) (* x30 x14 x39)) (* (- 1) (* x44 x31 x18)) (* (- 1) (* x31 x45 x22)) (* (- 1) (* x10 x31 x42)) (* (- 1) (* x14 x31 x43)) (* (- 1) (* x47 x14 x32)) (* (- 1) (* x48 x18 x32)) (* (- 1) (* x32 x49 x22)) (* (- 1) (* x10 x32 x46)) (* (- 1) (* x51 x14 x33)) (* (- 1) (* x10 x33 x50)) (* (- 1) (* x18 x52 x33)) (* (- 1) (* x22 x53 x33))) 0)) (>= (+ x3 (* (- 1) x28) (* (- 1) (* x30 x38 x11)) (* (- 1) (* x40 x30 x19)) (* (- 1) (* x30 x15 x39)) (* (- 1) (* x23 x30 x41)) (* (- 1) (* x44 x31 x19)) (* (- 1) (* x31 x11 x42)) (* (- 1) (* x31 x15 x43)) (* (- 1) (* x23 x31 x45)) (* (- 1) (* x47 x15 x32)) (* (- 1) (* x48 x32 x19)) (* (- 1) (* x11 x32 x46)) (* (- 1) (* x23 x32 x49)) (* (- 1) (* x51 x15 x33)) (* (- 1) (* x52 x19 x33)) (* (- 1) (* x11 x33 x50)) (* (- 1) (* x23 x53 x33))) 0)) (>= (+ x4 (* (- 1) x29) (* (- 1) (* x30 x38 x12)) (* (- 1) (* x30 x39 x16)) (* (- 1) (* x40 x30 x20)) (* (- 1) (* x30 x24 x41)) (* (- 1) (* x31 x42 x12)) (* (- 1) (* x31 x43 x16)) (* (- 1) (* x20 x44 x31)) (* (- 1) (* x24 x31 x45)) (* (- 1) (* x47 x32 x16)) (* (- 1) (* x32 x12 x46)) (* (- 1) (* x20 x48 x32)) (* (- 1) (* x24 x32 x49)) (* (- 1) (* x51 x16 x33)) (* (- 1) (* x12 x33 x50)) (* (- 1) (* x20 x52 x33)) (* (- 1) (* x24 x53 x33))) 0)))) (and (not (<= (+ x54 (* (- 1) x90) (* x74 x54) (* x75 x55) (* x76 x56) (* x57 x77)) 0)) (and (and (and (>= (+ x54 (* (- 1) x90) (* x74 x54) (* x75 x55) (* x76 x56) (* x57 x77)) 0) (>= (+ (* (- 1) x91) x55 (* x54 x78) (* x55 x79) (* x56 x80) (* x57 x81)) 0)) (>= (+ (* (- 1) x92) x56 (* x84 x56) (* x54 x82) (* x55 x83) (* x57 x85)) 0)) (>= (+ x57 (* (- 1) x93) (* x88 x56) (* x54 x86) (* x55 x87) (* x57 x89)) 0)))) (and (and (not (<= (+ (* (- 1) x54) x34 (* (- 1) (* x74 x34)) (* (- 1) (* x75 x35)) (* (- 1) (* x76 x36)) (* (- 1) (* x37 x77)) (* (- 1) (* x74 x38 x5)) (* (- 1) (* x40 x74 x7)) (* (- 1) (* x74 x41 x8)) (* (- 1) (* x6 x74 x39)) (* (- 1) (* x75 x42 x5)) (* (- 1) (* x44 x7 x75)) (* (- 1) (* x75 x45 x8)) (* (- 1) (* x6 x75 x43)) (* (- 1) (* x76 x5 x46)) (* (- 1) (* x6 x47 x76)) (* (- 1) (* x7 x48 x76)) (* (- 1) (* x8 x76 x49)) (* (- 1) (* x5 x77 x50)) (* (- 1) (* x6 x51 x77)) (* (- 1) (* x7 x52 x77)) (* (- 1) (* x8 x53 x77))) 0)) (and (and (and (>= (+ (* (- 1) x54) x34 (* (- 1) (* x74 x34)) (* (- 1) (* x75 x35)) (* (- 1) (* x76 x36)) (* (- 1) (* x37 x77)) (* (- 1) (* x74 x38 x5)) (* (- 1) (* x40 x74 x7)) (* (- 1) (* x74 x41 x8)) (* (- 1) (* x6 x74 x39)) (* (- 1) (* x75 x42 x5)) (* (- 1) (* x44 x7 x75)) (* (- 1) (* x75 x45 x8)) (* (- 1) (* x6 x75 x43)) (* (- 1) (* x76 x5 x46)) (* (- 1) (* x6 x47 x76)) (* (- 1) (* x7 x48 x76)) (* (- 1) (* x8 x76 x49)) (* (- 1) (* x5 x77 x50)) (* (- 1) (* x6 x51 x77)) (* (- 1) (* x7 x52 x77)) (* (- 1) (* x8 x53 x77))) 0) (>= (+ (* (- 1) x55) x35 (* (- 1) (* x78 x34)) (* (- 1) (* x79 x35)) (* (- 1) (* x80 x36)) (* (- 1) (* x81 x37)) (* (- 1) (* x78 x38 x5)) (* (- 1) (* x40 x78 x7)) (* (- 1) (* x78 x41 x8)) (* (- 1) (* x6 x78 x39)) (* (- 1) (* x79 x42 x5)) (* (- 1) (* x44 x7 x79)) (* (- 1) (* x45 x79 x8)) (* (- 1) (* x6 x79 x43)) (* (- 1) (* x5 x46 x80)) (* (- 1) (* x6 x47 x80)) (* (- 1) (* x7 x48 x80)) (* (- 1) (* x8 x49 x80)) (* (- 1) (* x81 x5 x50)) (* (- 1) (* x6 x81 x51)) (* (- 1) (* x81 x7 x52)) (* (- 1) (* x81 x8 x53))) 0)) (>= (+ (* (- 1) x56) x36 (* (- 1) (* x34 x82)) (* (- 1) (* x35 x83)) (* (- 1) (* x84 x36)) (* (- 1) (* x37 x85)) (* (- 1) (* x82 x38 x5)) (* (- 1) (* x40 x7 x82)) (* (- 1) (* x41 x82 x8)) (* (- 1) (* x6 x82 x39)) (* (- 1) (* x42 x5 x83)) (* (- 1) (* x44 x7 x83)) (* (- 1) (* x45 x8 x83)) (* (- 1) (* x6 x83 x43)) (* (- 1) (* x84 x5 x46)) (* (- 1) (* x6 x84 x47)) (* (- 1) (* x84 x7 x48)) (* (- 1) (* x84 x8 x49)) (* (- 1) (* x85 x5 x50)) (* (- 1) (* x6 x51 x85)) (* (- 1) (* x7 x85 x52)) (* (- 1) (* x85 x8 x53))) 0)) (>= (+ (* (- 1) x57) x37 (* (- 1) (* x34 x86)) (* (- 1) (* x35 x87)) (* (- 1) (* x88 x36)) (* (- 1) (* x37 x89)) (* (- 1) (* x38 x86 x5)) (* (- 1) (* x40 x7 x86)) (* (- 1) (* x41 x8 x86)) (* (- 1) (* x6 x86 x39)) (* (- 1) (* x42 x5 x87)) (* (- 1) (* x44 x7 x87)) (* (- 1) (* x45 x8 x87)) (* (- 1) (* x6 x87 x43)) (* (- 1) (* x88 x5 x46)) (* (- 1) (* x6 x47 x88)) (* (- 1) (* x88 x7 x48)) (* (- 1) (* x88 x8 x49)) (* (- 1) (* x89 x5 x50)) (* (- 1) (* x6 x51 x89)) (* (- 1) (* x7 x89 x52)) (* (- 1) (* x89 x8 x53))) 0))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (* (- 1) x58) x38 (* (- 1) (* x74 x38 x9)) (* (- 1) (* x40 x74 x17)) (* (- 1) (* x74 x41 x21)) (* (- 1) (* x74 x13 x39)) (* (- 1) (* x75 x42 x9)) (* (- 1) (* x44 x17 x75)) (* (- 1) (* x13 x75 x43)) (* (- 1) (* x75 x21 x45)) (* (- 1) (* x76 x46 x9)) (* (- 1) (* x13 x47 x76)) (* (- 1) (* x17 x48 x76)) (* (- 1) (* x21 x76 x49)) (* (- 1) (* x9 x77 x50)) (* (- 1) (* x13 x51 x77)) (* (- 1) (* x17 x52 x77)) (* (- 1) (* x21 x53 x77))) 0) (>= (+ (* (- 1) x59) x39 (* (- 1) (* x40 x74 x18)) (* (- 1) (* x74 x41 x22)) (* (- 1) (* x74 x10 x38)) (* (- 1) (* x74 x14 x39)) (* (- 1) (* x44 x75 x18)) (* (- 1) (* x75 x45 x22)) (* (- 1) (* x10 x75 x42)) (* (- 1) (* x75 x14 x43)) (* (- 1) (* x47 x14 x76)) (* (- 1) (* x48 x18 x76)) (* (- 1) (* x76 x49 x22)) (* (- 1) (* x10 x76 x46)) (* (- 1) (* x51 x14 x77)) (* (- 1) (* x10 x77 x50)) (* (- 1) (* x18 x52 x77)) (* (- 1) (* x22 x53 x77))) 0)) (>= (+ x40 (* (- 1) x60) (* (- 1) (* x74 x38 x11)) (* (- 1) (* x40 x74 x19)) (* (- 1) (* x74 x15 x39)) (* (- 1) (* x23 x74 x41)) (* (- 1) (* x44 x75 x19)) (* (- 1) (* x75 x11 x42)) (* (- 1) (* x75 x15 x43)) (* (- 1) (* x23 x75 x45)) (* (- 1) (* x47 x76 x15)) (* (- 1) (* x48 x76 x19)) (* (- 1) (* x11 x76 x46)) (* (- 1) (* x23 x76 x49)) (* (- 1) (* x51 x15 x77)) (* (- 1) (* x52 x19 x77)) (* (- 1) (* x11 x77 x50)) (* (- 1) (* x23 x53 x77))) 0)) (>= (+ (* (- 1) x61) x41 (* (- 1) (* x74 x38 x12)) (* (- 1) (* x74 x39 x16)) (* (- 1) (* x40 x74 x20)) (* (- 1) (* x74 x24 x41)) (* (- 1) (* x75 x42 x12)) (* (- 1) (* x75 x43 x16)) (* (- 1) (* x20 x44 x75)) (* (- 1) (* x24 x75 x45)) (* (- 1) (* x47 x76 x16)) (* (- 1) (* x76 x12 x46)) (* (- 1) (* x20 x48 x76)) (* (- 1) (* x24 x76 x49)) (* (- 1) (* x51 x77 x16)) (* (- 1) (* x12 x77 x50)) (* (- 1) (* x20 x52 x77)) (* (- 1) (* x24 x53 x77))) 0)) (>= (+ (* (- 1) x62) x42 (* (- 1) (* x78 x38 x9)) (* (- 1) (* x40 x78 x17)) (* (- 1) (* x78 x41 x21)) (* (- 1) (* x13 x78 x39)) (* (- 1) (* x79 x42 x9)) (* (- 1) (* x44 x17 x79)) (* (- 1) (* x13 x79 x43)) (* (- 1) (* x21 x45 x79)) (* (- 1) (* x46 x80 x9)) (* (- 1) (* x13 x47 x80)) (* (- 1) (* x17 x48 x80)) (* (- 1) (* x21 x49 x80)) (* (- 1) (* x81 x9 x50)) (* (- 1) (* x13 x81 x51)) (* (- 1) (* x81 x17 x52)) (* (- 1) (* x81 x21 x53))) 0)) (>= (+ (* (- 1) x63) x43 (* (- 1) (* x40 x78 x18)) (* (- 1) (* x78 x41 x22)) (* (- 1) (* x10 x78 x38)) (* (- 1) (* x78 x14 x39)) (* (- 1) (* x44 x79 x18)) (* (- 1) (* x45 x79 x22)) (* (- 1) (* x10 x79 x42)) (* (- 1) (* x14 x79 x43)) (* (- 1) (* x47 x14 x80)) (* (- 1) (* x48 x18 x80)) (* (- 1) (* x49 x22 x80)) (* (- 1) (* x10 x46 x80)) (* (- 1) (* x81 x51 x14)) (* (- 1) (* x81 x10 x50)) (* (- 1) (* x81 x18 x52)) (* (- 1) (* x81 x22 x53))) 0)) (>= (+ (* (- 1) x64) x44 (* (- 1) (* x78 x38 x11)) (* (- 1) (* x40 x78 x19)) (* (- 1) (* x78 x15 x39)) (* (- 1) (* x23 x78 x41)) (* (- 1) (* x44 x79 x19)) (* (- 1) (* x11 x79 x42)) (* (- 1) (* x79 x15 x43)) (* (- 1) (* x23 x45 x79)) (* (- 1) (* x47 x15 x80)) (* (- 1) (* x48 x80 x19)) (* (- 1) (* x11 x46 x80)) (* (- 1) (* x23 x49 x80)) (* (- 1) (* x81 x51 x15)) (* (- 1) (* x81 x52 x19)) (* (- 1) (* x81 x11 x50)) (* (- 1) (* x23 x81 x53))) 0)) (>= (+ (* (- 1) x65) x45 (* (- 1) (* x78 x38 x12)) (* (- 1) (* x78 x39 x16)) (* (- 1) (* x40 x20 x78)) (* (- 1) (* x78 x24 x41)) (* (- 1) (* x79 x42 x12)) (* (- 1) (* x79 x43 x16)) (* (- 1) (* x20 x44 x79)) (* (- 1) (* x24 x45 x79)) (* (- 1) (* x47 x80 x16)) (* (- 1) (* x12 x46 x80)) (* (- 1) (* x20 x48 x80)) (* (- 1) (* x24 x49 x80)) (* (- 1) (* x81 x51 x16)) (* (- 1) (* x81 x12 x50)) (* (- 1) (* x81 x20 x52)) (* (- 1) (* x81 x24 x53))) 0)) (>= (+ (* (- 1) x66) x46 (* (- 1) (* x82 x38 x9)) (* (- 1) (* x40 x17 x82)) (* (- 1) (* x41 x82 x21)) (* (- 1) (* x13 x82 x39)) (* (- 1) (* x42 x83 x9)) (* (- 1) (* x44 x17 x83)) (* (- 1) (* x13 x83 x43)) (* (- 1) (* x21 x45 x83)) (* (- 1) (* x84 x46 x9)) (* (- 1) (* x84 x13 x47)) (* (- 1) (* x84 x17 x48)) (* (- 1) (* x84 x21 x49)) (* (- 1) (* x85 x9 x50)) (* (- 1) (* x13 x51 x85)) (* (- 1) (* x17 x85 x52)) (* (- 1) (* x85 x21 x53))) 0)) (>= (+ x47 (* (- 1) x67) (* (- 1) (* x40 x82 x18)) (* (- 1) (* x41 x82 x22)) (* (- 1) (* x10 x82 x38)) (* (- 1) (* x14 x82 x39)) (* (- 1) (* x44 x18 x83)) (* (- 1) (* x45 x83 x22)) (* (- 1) (* x10 x42 x83)) (* (- 1) (* x14 x83 x43)) (* (- 1) (* x84 x47 x14)) (* (- 1) (* x84 x48 x18)) (* (- 1) (* x84 x49 x22)) (* (- 1) (* x84 x10 x46)) (* (- 1) (* x51 x85 x14)) (* (- 1) (* x10 x85 x50)) (* (- 1) (* x85 x18 x52)) (* (- 1) (* x85 x22 x53))) 0)) (>= (+ (* (- 1) x68) x48 (* (- 1) (* x82 x38 x11)) (* (- 1) (* x40 x82 x19)) (* (- 1) (* x82 x15 x39)) (* (- 1) (* x23 x41 x82)) (* (- 1) (* x44 x83 x19)) (* (- 1) (* x11 x42 x83)) (* (- 1) (* x15 x83 x43)) (* (- 1) (* x23 x45 x83)) (* (- 1) (* x84 x47 x15)) (* (- 1) (* x84 x48 x19)) (* (- 1) (* x84 x11 x46)) (* (- 1) (* x84 x23 x49)) (* (- 1) (* x51 x85 x15)) (* (- 1) (* x85 x52 x19)) (* (- 1) (* x85 x11 x50)) (* (- 1) (* x23 x85 x53))) 0)) (>= (+ (* (- 1) x69) x49 (* (- 1) (* x82 x38 x12)) (* (- 1) (* x82 x39 x16)) (* (- 1) (* x40 x20 x82)) (* (- 1) (* x24 x41 x82)) (* (- 1) (* x42 x83 x12)) (* (- 1) (* x83 x43 x16)) (* (- 1) (* x20 x44 x83)) (* (- 1) (* x24 x45 x83)) (* (- 1) (* x84 x47 x16)) (* (- 1) (* x84 x12 x46)) (* (- 1) (* x84 x20 x48)) (* (- 1) (* x84 x24 x49)) (* (- 1) (* x51 x85 x16)) (* (- 1) (* x85 x12 x50)) (* (- 1) (* x20 x85 x52)) (* (- 1) (* x85 x24 x53))) 0)) (>= (+ (* (- 1) x70) x50 (* (- 1) (* x38 x86 x9)) (* (- 1) (* x40 x17 x86)) (* (- 1) (* x41 x21 x86)) (* (- 1) (* x13 x86 x39)) (* (- 1) (* x42 x9 x87)) (* (- 1) (* x44 x17 x87)) (* (- 1) (* x13 x87 x43)) (* (- 1) (* x21 x45 x87)) (* (- 1) (* x88 x46 x9)) (* (- 1) (* x13 x47 x88)) (* (- 1) (* x88 x17 x48)) (* (- 1) (* x88 x21 x49)) (* (- 1) (* x89 x9 x50)) (* (- 1) (* x13 x51 x89)) (* (- 1) (* x17 x89 x52)) (* (- 1) (* x21 x89 x53))) 0)) (>= (+ (* (- 1) x71) x51 (* (- 1) (* x40 x18 x86)) (* (- 1) (* x41 x86 x22)) (* (- 1) (* x10 x38 x86)) (* (- 1) (* x14 x86 x39)) (* (- 1) (* x44 x18 x87)) (* (- 1) (* x45 x22 x87)) (* (- 1) (* x10 x42 x87)) (* (- 1) (* x14 x87 x43)) (* (- 1) (* x47 x88 x14)) (* (- 1) (* x88 x48 x18)) (* (- 1) (* x88 x49 x22)) (* (- 1) (* x10 x88 x46)) (* (- 1) (* x51 x14 x89)) (* (- 1) (* x10 x89 x50)) (* (- 1) (* x89 x18 x52)) (* (- 1) (* x89 x22 x53))) 0)) (>= (+ (* (- 1) x72) x52 (* (- 1) (* x38 x11 x86)) (* (- 1) (* x40 x86 x19)) (* (- 1) (* x86 x15 x39)) (* (- 1) (* x23 x41 x86)) (* (- 1) (* x44 x19 x87)) (* (- 1) (* x11 x42 x87)) (* (- 1) (* x15 x87 x43)) (* (- 1) (* x23 x45 x87)) (* (- 1) (* x47 x88 x15)) (* (- 1) (* x88 x48 x19)) (* (- 1) (* x88 x11 x46)) (* (- 1) (* x23 x88 x49)) (* (- 1) (* x51 x89 x15)) (* (- 1) (* x89 x52 x19)) (* (- 1) (* x11 x89 x50)) (* (- 1) (* x23 x89 x53))) 0)) (>= (+ (* (- 1) x73) x53 (* (- 1) (* x38 x86 x12)) (* (- 1) (* x86 x39 x16)) (* (- 1) (* x40 x20 x86)) (* (- 1) (* x24 x41 x86)) (* (- 1) (* x42 x12 x87)) (* (- 1) (* x87 x43 x16)) (* (- 1) (* x20 x44 x87)) (* (- 1) (* x24 x45 x87)) (* (- 1) (* x47 x88 x16)) (* (- 1) (* x88 x12 x46)) (* (- 1) (* x20 x88 x48)) (* (- 1) (* x88 x24 x49)) (* (- 1) (* x51 x89 x16)) (* (- 1) (* x89 x12 x50)) (* (- 1) (* x20 x89 x52)) (* (- 1) (* x24 x89 x53))) 0)))) (and (and (and (not (<= (+ (* (- 1) (* x1 x5)) (* (- 1) (* x3 x7)) (* (- 1) (* x4 x8)) (* (- 1) (* x6 x2))) 0)) (>= (+ (* (- 1) (* x1 x5)) (* (- 1) (* x3 x7)) (* (- 1) (* x4 x8)) (* (- 1) (* x6 x2))) 0)) (and (and (and (>= (+ x1 (* (- 1) (* x1 x9)) (* (- 1) (* x3 x17)) (* (- 1) (* x4 x21)) (* (- 1) (* x13 x2))) 0) (>= (+ x2 (* (- 1) (* x3 x18)) (* (- 1) (* x4 x22)) (* (- 1) (* x10 x1)) (* (- 1) (* x14 x2))) 0)) (>= (+ x3 (* (- 1) (* x3 x19)) (* (- 1) (* x11 x1)) (* (- 1) (* x15 x2)) (* (- 1) (* x23 x4))) 0)) (>= (+ x4 (* (- 1) (* x1 x12)) (* (- 1) (* x2 x16)) (* (- 1) (* x3 x20)) (* (- 1) (* x24 x4))) 0))) (and (and (not (<= (+ x0 (* (- 1) x25) (* (- 1) (* x30 x34)) (* (- 1) (* x31 x35)) (* (- 1) (* x32 x36)) (* (- 1) (* x37 x33)) (* (- 1) (* x30 x38 x5)) (* (- 1) (* x40 x30 x7)) (* (- 1) (* x30 x41 x8)) (* (- 1) (* x6 x30 x39)) (* (- 1) (* x31 x42 x5)) (* (- 1) (* x44 x7 x31)) (* (- 1) (* x31 x45 x8)) (* (- 1) (* x6 x31 x43)) (* (- 1) (* x32 x5 x46)) (* (- 1) (* x6 x47 x32)) (* (- 1) (* x7 x48 x32)) (* (- 1) (* x8 x32 x49)) (* (- 1) (* x5 x33 x50)) (* (- 1) (* x6 x51 x33)) (* (- 1) (* x7 x52 x33)) (* (- 1) (* x8 x53 x33))) 0)) (>= (+ x0 (* (- 1) x25) (* (- 1) (* x30 x34)) (* (- 1) (* x31 x35)) (* (- 1) (* x32 x36)) (* (- 1) (* x37 x33)) (* (- 1) (* x30 x38 x5)) (* (- 1) (* x40 x30 x7)) (* (- 1) (* x30 x41 x8)) (* (- 1) (* x6 x30 x39)) (* (- 1) (* x31 x42 x5)) (* (- 1) (* x44 x7 x31)) (* (- 1) (* x31 x45 x8)) (* (- 1) (* x6 x31 x43)) (* (- 1) (* x32 x5 x46)) (* (- 1) (* x6 x47 x32)) (* (- 1) (* x7 x48 x32)) (* (- 1) (* x8 x32 x49)) (* (- 1) (* x5 x33 x50)) (* (- 1) (* x6 x51 x33)) (* (- 1) (* x7 x52 x33)) (* (- 1) (* x8 x53 x33))) 0)) (and (and (and (>= (+ x1 (* (- 1) x26) (* (- 1) (* x30 x38 x9)) (* (- 1) (* x40 x30 x17)) (* (- 1) (* x30 x41 x21)) (* (- 1) (* x13 x30 x39)) (* (- 1) (* x31 x42 x9)) (* (- 1) (* x44 x17 x31)) (* (- 1) (* x13 x31 x43)) (* (- 1) (* x31 x21 x45)) (* (- 1) (* x32 x46 x9)) (* (- 1) (* x13 x47 x32)) (* (- 1) (* x17 x48 x32)) (* (- 1) (* x21 x32 x49)) (* (- 1) (* x9 x33 x50)) (* (- 1) (* x13 x51 x33)) (* (- 1) (* x17 x52 x33)) (* (- 1) (* x21 x53 x33))) 0) (>= (+ (* (- 1) x27) x2 (* (- 1) (* x40 x30 x18)) (* (- 1) (* x30 x41 x22)) (* (- 1) (* x30 x10 x38)) (* (- 1) (* x30 x14 x39)) (* (- 1) (* x44 x31 x18)) (* (- 1) (* x31 x45 x22)) (* (- 1) (* x10 x31 x42)) (* (- 1) (* x14 x31 x43)) (* (- 1) (* x47 x14 x32)) (* (- 1) (* x48 x18 x32)) (* (- 1) (* x32 x49 x22)) (* (- 1) (* x10 x32 x46)) (* (- 1) (* x51 x14 x33)) (* (- 1) (* x10 x33 x50)) (* (- 1) (* x18 x52 x33)) (* (- 1) (* x22 x53 x33))) 0)) (>= (+ x3 (* (- 1) x28) (* (- 1) (* x30 x38 x11)) (* (- 1) (* x40 x30 x19)) (* (- 1) (* x30 x15 x39)) (* (- 1) (* x23 x30 x41)) (* (- 1) (* x44 x31 x19)) (* (- 1) (* x31 x11 x42)) (* (- 1) (* x31 x15 x43)) (* (- 1) (* x23 x31 x45)) (* (- 1) (* x47 x15 x32)) (* (- 1) (* x48 x32 x19)) (* (- 1) (* x11 x32 x46)) (* (- 1) (* x23 x32 x49)) (* (- 1) (* x51 x15 x33)) (* (- 1) (* x52 x19 x33)) (* (- 1) (* x11 x33 x50)) (* (- 1) (* x23 x53 x33))) 0)) (>= (+ x4 (* (- 1) x29) (* (- 1) (* x30 x38 x12)) (* (- 1) (* x30 x39 x16)) (* (- 1) (* x40 x30 x20)) (* (- 1) (* x30 x24 x41)) (* (- 1) (* x31 x42 x12)) (* (- 1) (* x31 x43 x16)) (* (- 1) (* x20 x44 x31)) (* (- 1) (* x24 x31 x45)) (* (- 1) (* x47 x32 x16)) (* (- 1) (* x32 x12 x46)) (* (- 1) (* x20 x48 x32)) (* (- 1) (* x24 x32 x49)) (* (- 1) (* x51 x16 x33)) (* (- 1) (* x12 x33 x50)) (* (- 1) (* x20 x52 x33)) (* (- 1) (* x24 x53 x33))) 0))))))
(exit)
(check-sat)
