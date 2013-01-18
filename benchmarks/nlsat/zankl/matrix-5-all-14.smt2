(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x145 () Real)
(declare-fun x6 () Real)
(declare-fun x84 () Real)
(declare-fun x23 () Real)
(declare-fun x101 () Real)
(declare-fun x179 () Real)
(declare-fun x40 () Real)
(declare-fun x118 () Real)
(declare-fun x196 () Real)
(declare-fun x57 () Real)
(declare-fun x135 () Real)
(declare-fun x74 () Real)
(declare-fun x13 () Real)
(declare-fun x91 () Real)
(declare-fun x30 () Real)
(declare-fun x108 () Real)
(declare-fun x186 () Real)
(declare-fun x47 () Real)
(declare-fun x125 () Real)
(declare-fun x64 () Real)
(declare-fun x142 () Real)
(declare-fun x3 () Real)
(declare-fun x81 () Real)
(declare-fun x20 () Real)
(declare-fun x98 () Real)
(declare-fun x176 () Real)
(declare-fun x37 () Real)
(declare-fun x115 () Real)
(declare-fun x193 () Real)
(declare-fun x54 () Real)
(declare-fun x132 () Real)
(declare-fun x71 () Real)
(declare-fun x10 () Real)
(declare-fun x88 () Real)
(declare-fun x27 () Real)
(declare-fun x105 () Real)
(declare-fun x183 () Real)
(declare-fun x44 () Real)
(declare-fun x122 () Real)
(declare-fun x61 () Real)
(declare-fun x139 () Real)
(declare-fun x0 () Real)
(declare-fun x78 () Real)
(declare-fun x17 () Real)
(declare-fun x95 () Real)
(declare-fun x173 () Real)
(declare-fun x34 () Real)
(declare-fun x112 () Real)
(declare-fun x190 () Real)
(declare-fun x51 () Real)
(declare-fun x129 () Real)
(declare-fun x68 () Real)
(declare-fun x146 () Real)
(declare-fun x7 () Real)
(declare-fun x85 () Real)
(declare-fun x24 () Real)
(declare-fun x102 () Real)
(declare-fun x180 () Real)
(declare-fun x41 () Real)
(declare-fun x119 () Real)
(declare-fun x58 () Real)
(declare-fun x136 () Real)
(declare-fun x75 () Real)
(declare-fun x14 () Real)
(declare-fun x92 () Real)
(declare-fun x31 () Real)
(declare-fun x109 () Real)
(declare-fun x187 () Real)
(declare-fun x48 () Real)
(declare-fun x126 () Real)
(declare-fun x65 () Real)
(declare-fun x143 () Real)
(declare-fun x4 () Real)
(declare-fun x82 () Real)
(declare-fun x21 () Real)
(declare-fun x99 () Real)
(declare-fun x177 () Real)
(declare-fun x38 () Real)
(declare-fun x116 () Real)
(declare-fun x194 () Real)
(declare-fun x55 () Real)
(declare-fun x133 () Real)
(declare-fun x72 () Real)
(declare-fun x11 () Real)
(declare-fun x89 () Real)
(declare-fun x28 () Real)
(declare-fun x106 () Real)
(declare-fun x184 () Real)
(declare-fun x45 () Real)
(declare-fun x123 () Real)
(declare-fun x62 () Real)
(declare-fun x140 () Real)
(declare-fun x1 () Real)
(declare-fun x79 () Real)
(declare-fun x18 () Real)
(declare-fun x96 () Real)
(declare-fun x174 () Real)
(declare-fun x35 () Real)
(declare-fun x113 () Real)
(declare-fun x191 () Real)
(declare-fun x52 () Real)
(declare-fun x130 () Real)
(declare-fun x69 () Real)
(declare-fun x8 () Real)
(declare-fun x86 () Real)
(declare-fun x25 () Real)
(declare-fun x103 () Real)
(declare-fun x181 () Real)
(declare-fun x42 () Real)
(declare-fun x120 () Real)
(declare-fun x59 () Real)
(declare-fun x137 () Real)
(declare-fun x76 () Real)
(declare-fun x15 () Real)
(declare-fun x93 () Real)
(declare-fun x32 () Real)
(declare-fun x110 () Real)
(declare-fun x188 () Real)
(declare-fun x49 () Real)
(declare-fun x127 () Real)
(declare-fun x66 () Real)
(declare-fun x144 () Real)
(declare-fun x5 () Real)
(declare-fun x83 () Real)
(declare-fun x22 () Real)
(declare-fun x100 () Real)
(declare-fun x178 () Real)
(declare-fun x39 () Real)
(declare-fun x117 () Real)
(declare-fun x195 () Real)
(declare-fun x56 () Real)
(declare-fun x134 () Real)
(declare-fun x73 () Real)
(declare-fun x12 () Real)
(declare-fun x90 () Real)
(declare-fun x29 () Real)
(declare-fun x107 () Real)
(declare-fun x185 () Real)
(declare-fun x46 () Real)
(declare-fun x124 () Real)
(declare-fun x63 () Real)
(declare-fun x141 () Real)
(declare-fun x2 () Real)
(declare-fun x80 () Real)
(declare-fun x19 () Real)
(declare-fun x97 () Real)
(declare-fun x175 () Real)
(declare-fun x36 () Real)
(declare-fun x114 () Real)
(declare-fun x192 () Real)
(declare-fun x53 () Real)
(declare-fun x131 () Real)
(declare-fun x70 () Real)
(declare-fun x9 () Real)
(declare-fun x87 () Real)
(declare-fun x26 () Real)
(declare-fun x104 () Real)
(declare-fun x182 () Real)
(declare-fun x43 () Real)
(declare-fun x121 () Real)
(declare-fun x60 () Real)
(declare-fun x138 () Real)
(declare-fun x77 () Real)
(declare-fun x16 () Real)
(declare-fun x94 () Real)
(declare-fun x172 () Real)
(declare-fun x33 () Real)
(declare-fun x111 () Real)
(declare-fun x189 () Real)
(declare-fun x50 () Real)
(declare-fun x128 () Real)
(declare-fun x67 () Real)
(assert (>= x145 0))
(assert (>= x6 0))
(assert (>= x84 0))
(assert (>= x23 0))
(assert (>= x101 0))
(assert (>= x179 0))
(assert (>= x40 0))
(assert (>= x118 0))
(assert (>= x196 0))
(assert (>= x57 0))
(assert (>= x135 0))
(assert (>= x74 0))
(assert (>= x13 0))
(assert (>= x91 0))
(assert (>= x30 0))
(assert (>= x108 0))
(assert (>= x186 0))
(assert (>= x47 0))
(assert (>= x125 0))
(assert (>= x64 0))
(assert (>= x142 0))
(assert (>= x3 0))
(assert (>= x81 0))
(assert (>= x20 0))
(assert (>= x98 0))
(assert (>= x176 0))
(assert (>= x37 0))
(assert (>= x115 0))
(assert (>= x193 0))
(assert (>= x54 0))
(assert (>= x132 0))
(assert (>= x71 0))
(assert (>= x10 0))
(assert (>= x88 0))
(assert (>= x27 0))
(assert (>= x105 0))
(assert (>= x183 0))
(assert (>= x44 0))
(assert (>= x122 0))
(assert (>= x61 0))
(assert (>= x139 0))
(assert (>= x0 0))
(assert (>= x78 0))
(assert (>= x17 0))
(assert (>= x95 0))
(assert (>= x173 0))
(assert (>= x34 0))
(assert (>= x112 0))
(assert (>= x190 0))
(assert (>= x51 0))
(assert (>= x129 0))
(assert (>= x68 0))
(assert (>= x146 0))
(assert (>= x7 0))
(assert (>= x85 0))
(assert (>= x24 0))
(assert (>= x102 0))
(assert (>= x180 0))
(assert (>= x41 0))
(assert (>= x119 0))
(assert (>= x58 0))
(assert (>= x136 0))
(assert (>= x75 0))
(assert (>= x14 0))
(assert (>= x92 0))
(assert (>= x31 0))
(assert (>= x109 0))
(assert (>= x187 0))
(assert (>= x48 0))
(assert (>= x126 0))
(assert (>= x65 0))
(assert (>= x143 0))
(assert (>= x4 0))
(assert (>= x82 0))
(assert (>= x21 0))
(assert (>= x99 0))
(assert (>= x177 0))
(assert (>= x38 0))
(assert (>= x116 0))
(assert (>= x194 0))
(assert (>= x55 0))
(assert (>= x133 0))
(assert (>= x72 0))
(assert (>= x11 0))
(assert (>= x89 0))
(assert (>= x28 0))
(assert (>= x106 0))
(assert (>= x184 0))
(assert (>= x45 0))
(assert (>= x123 0))
(assert (>= x62 0))
(assert (>= x140 0))
(assert (>= x1 0))
(assert (>= x79 0))
(assert (>= x18 0))
(assert (>= x96 0))
(assert (>= x174 0))
(assert (>= x35 0))
(assert (>= x113 0))
(assert (>= x191 0))
(assert (>= x52 0))
(assert (>= x130 0))
(assert (>= x69 0))
(assert (>= x8 0))
(assert (>= x86 0))
(assert (>= x25 0))
(assert (>= x103 0))
(assert (>= x181 0))
(assert (>= x42 0))
(assert (>= x120 0))
(assert (>= x59 0))
(assert (>= x137 0))
(assert (>= x76 0))
(assert (>= x15 0))
(assert (>= x93 0))
(assert (>= x32 0))
(assert (>= x110 0))
(assert (>= x188 0))
(assert (>= x49 0))
(assert (>= x127 0))
(assert (>= x66 0))
(assert (>= x144 0))
(assert (>= x5 0))
(assert (>= x83 0))
(assert (>= x22 0))
(assert (>= x100 0))
(assert (>= x178 0))
(assert (>= x39 0))
(assert (>= x117 0))
(assert (>= x195 0))
(assert (>= x56 0))
(assert (>= x134 0))
(assert (>= x73 0))
(assert (>= x12 0))
(assert (>= x90 0))
(assert (>= x29 0))
(assert (>= x107 0))
(assert (>= x185 0))
(assert (>= x46 0))
(assert (>= x124 0))
(assert (>= x63 0))
(assert (>= x141 0))
(assert (>= x2 0))
(assert (>= x80 0))
(assert (>= x19 0))
(assert (>= x97 0))
(assert (>= x175 0))
(assert (>= x36 0))
(assert (>= x114 0))
(assert (>= x192 0))
(assert (>= x53 0))
(assert (>= x131 0))
(assert (>= x70 0))
(assert (>= x9 0))
(assert (>= x87 0))
(assert (>= x26 0))
(assert (>= x104 0))
(assert (>= x182 0))
(assert (>= x43 0))
(assert (>= x121 0))
(assert (>= x60 0))
(assert (>= x138 0))
(assert (>= x77 0))
(assert (>= x16 0))
(assert (>= x94 0))
(assert (>= x172 0))
(assert (>= x33 0))
(assert (>= x111 0))
(assert (>= x189 0))
(assert (>= x50 0))
(assert (>= x128 0))
(assert (>= x67 0))
(assert (let ((?v_0 (+ (+ x0 (+ (+ (+ (+ (* x1 x6) (* x2 x7)) (* x3 x8)) (* x4 x9)) (* x5 x10))) (+ (+ (+ (+ (* x11 x16) (* x12 x17)) (* x13 x18)) (* x14 x19)) (* x15 x20)))) (?v_1 (+ (+ x0 (+ (+ (+ (+ (* x1 x32) (* x2 x33)) (* x3 x34)) (* x4 x35)) (* x5 x36))) (+ (+ (+ (+ (* x11 x32) (* x12 x33)) (* x13 x34)) (* x14 x35)) (* x15 x36))))) (let ((?v_6 (and (and (and (> ?v_0 x26) (>= ?v_0 x26)) (and (and (and (and (>= x21 x27) (>= x22 x28)) (>= x23 x29)) (>= x24 x30)) (>= x25 x31))) (and (and (> ?v_0 ?v_1) (>= ?v_0 ?v_1)) (and (and (and (and (>= x21 (+ (+ (+ (+ (+ (+ (* x1 x37) (* x2 x42)) (* x3 x47)) (* x4 x52)) (* x5 x57)) (+ (+ (+ (+ (* x11 x37) (* x12 x42)) (* x13 x47)) (* x14 x52)) (* x15 x57))) x21)) (>= x22 (+ (+ (+ (+ (+ (+ (* x1 x38) (* x2 x43)) (* x3 x48)) (* x4 x53)) (* x5 x58)) (+ (+ (+ (+ (* x11 x38) (* x12 x43)) (* x13 x48)) (* x14 x53)) (* x15 x58))) x22))) (>= x23 (+ (+ (+ (+ (+ (+ (* x1 x39) (* x2 x44)) (* x3 x49)) (* x4 x54)) (* x5 x59)) (+ (+ (+ (+ (* x11 x39) (* x12 x44)) (* x13 x49)) (* x14 x54)) (* x15 x59))) x23))) (>= x24 (+ (+ (+ (+ (+ (+ (* x1 x40) (* x2 x45)) (* x3 x50)) (* x4 x55)) (* x5 x60)) (+ (+ (+ (+ (* x11 x40) (* x12 x45)) (* x13 x50)) (* x14 x55)) (* x15 x60))) x24))) (>= x25 (+ (+ (+ (+ (+ (+ (* x1 x41) (* x2 x46)) (* x3 x51)) (* x4 x56)) (* x5 x61)) (+ (+ (+ (+ (* x11 x41) (* x12 x46)) (* x13 x51)) (* x14 x56)) (* x15 x61))) x25)))))) (?v_3 (+ (+ x62 (+ (+ (+ (+ (* x67 x32) (* x68 x33)) (* x69 x34)) (* x70 x35)) (* x71 x36))) (+ (+ (+ (+ (* x92 x32) (* x93 x33)) (* x94 x34)) (* x95 x35)) (* x96 x36)))) (?v_2 (+ (+ x62 (+ (+ (+ (+ (* x67 x6) (* x68 x7)) (* x69 x8)) (* x70 x9)) (* x71 x10))) (+ (+ (+ (+ (* x92 x16) (* x93 x17)) (* x94 x18)) (* x95 x19)) (* x96 x20)))) (?v_4 (+ x32 (+ (+ (+ (+ (* x37 x6) (* x38 x7)) (* x39 x8)) (* x40 x9)) (* x41 x10)))) (?v_5 (+ x32 (+ (+ (+ (+ (* x37 x142) (* x38 x143)) (* x39 x144)) (* x40 x145)) (* x41 x146))))) (and (and (and (and ?v_6 (and (and (> ?v_2 ?v_3) (and (and (and (and (>= ?v_2 ?v_3) (>= (+ (+ x63 (+ (+ (+ (+ (* x72 x6) (* x73 x7)) (* x74 x8)) (* x75 x9)) (* x76 x10))) (+ (+ (+ (+ (* x97 x16) (* x98 x17)) (* x99 x18)) (* x100 x19)) (* x101 x20))) (+ (+ x63 (+ (+ (+ (+ (* x72 x32) (* x73 x33)) (* x74 x34)) (* x75 x35)) (* x76 x36))) (+ (+ (+ (+ (* x97 x32) (* x98 x33)) (* x99 x34)) (* x100 x35)) (* x101 x36))))) (>= (+ (+ x64 (+ (+ (+ (+ (* x77 x6) (* x78 x7)) (* x79 x8)) (* x80 x9)) (* x81 x10))) (+ (+ (+ (+ (* x102 x16) (* x103 x17)) (* x104 x18)) (* x105 x19)) (* x106 x20))) (+ (+ x64 (+ (+ (+ (+ (* x77 x32) (* x78 x33)) (* x79 x34)) (* x80 x35)) (* x81 x36))) (+ (+ (+ (+ (* x102 x32) (* x103 x33)) (* x104 x34)) (* x105 x35)) (* x106 x36))))) (>= (+ (+ x65 (+ (+ (+ (+ (* x82 x6) (* x83 x7)) (* x84 x8)) (* x85 x9)) (* x86 x10))) (+ (+ (+ (+ (* x107 x16) (* x108 x17)) (* x109 x18)) (* x110 x19)) (* x111 x20))) (+ (+ x65 (+ (+ (+ (+ (* x82 x32) (* x83 x33)) (* x84 x34)) (* x85 x35)) (* x86 x36))) (+ (+ (+ (+ (* x107 x32) (* x108 x33)) (* x109 x34)) (* x110 x35)) (* x111 x36))))) (>= (+ (+ x66 (+ (+ (+ (+ (* x87 x6) (* x88 x7)) (* x89 x8)) (* x90 x9)) (* x91 x10))) (+ (+ (+ (+ (* x112 x16) (* x113 x17)) (* x114 x18)) (* x115 x19)) (* x116 x20))) (+ (+ x66 (+ (+ (+ (+ (* x87 x32) (* x88 x33)) (* x89 x34)) (* x90 x35)) (* x91 x36))) (+ (+ (+ (+ (* x112 x32) (* x113 x33)) (* x114 x34)) (* x115 x35)) (* x116 x36)))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= x117 (+ (+ (+ (+ (+ (+ (* x67 x37) (* x68 x42)) (* x69 x47)) (* x70 x52)) (* x71 x57)) (+ (+ (+ (+ (* x92 x37) (* x93 x42)) (* x94 x47)) (* x95 x52)) (* x96 x57))) x117)) (>= x118 (+ (+ (+ (+ (+ (+ (* x67 x38) (* x68 x43)) (* x69 x48)) (* x70 x53)) (* x71 x58)) (+ (+ (+ (+ (* x92 x38) (* x93 x43)) (* x94 x48)) (* x95 x53)) (* x96 x58))) x118))) (>= x119 (+ (+ (+ (+ (+ (+ (* x67 x39) (* x68 x44)) (* x69 x49)) (* x70 x54)) (* x71 x59)) (+ (+ (+ (+ (* x92 x39) (* x93 x44)) (* x94 x49)) (* x95 x54)) (* x96 x59))) x119))) (>= x120 (+ (+ (+ (+ (+ (+ (* x67 x40) (* x68 x45)) (* x69 x50)) (* x70 x55)) (* x71 x60)) (+ (+ (+ (+ (* x92 x40) (* x93 x45)) (* x94 x50)) (* x95 x55)) (* x96 x60))) x120))) (>= x121 (+ (+ (+ (+ (+ (+ (* x67 x41) (* x68 x46)) (* x69 x51)) (* x70 x56)) (* x71 x61)) (+ (+ (+ (+ (* x92 x41) (* x93 x46)) (* x94 x51)) (* x95 x56)) (* x96 x61))) x121))) (>= x122 (+ (+ (+ (+ (+ (+ (* x72 x37) (* x73 x42)) (* x74 x47)) (* x75 x52)) (* x76 x57)) (+ (+ (+ (+ (* x97 x37) (* x98 x42)) (* x99 x47)) (* x100 x52)) (* x101 x57))) x122))) (>= x123 (+ (+ (+ (+ (+ (+ (* x72 x38) (* x73 x43)) (* x74 x48)) (* x75 x53)) (* x76 x58)) (+ (+ (+ (+ (* x97 x38) (* x98 x43)) (* x99 x48)) (* x100 x53)) (* x101 x58))) x123))) (>= x124 (+ (+ (+ (+ (+ (+ (* x72 x39) (* x73 x44)) (* x74 x49)) (* x75 x54)) (* x76 x59)) (+ (+ (+ (+ (* x97 x39) (* x98 x44)) (* x99 x49)) (* x100 x54)) (* x101 x59))) x124))) (>= x125 (+ (+ (+ (+ (+ (+ (* x72 x40) (* x73 x45)) (* x74 x50)) (* x75 x55)) (* x76 x60)) (+ (+ (+ (+ (* x97 x40) (* x98 x45)) (* x99 x50)) (* x100 x55)) (* x101 x60))) x125))) (>= x126 (+ (+ (+ (+ (+ (+ (* x72 x41) (* x73 x46)) (* x74 x51)) (* x75 x56)) (* x76 x61)) (+ (+ (+ (+ (* x97 x41) (* x98 x46)) (* x99 x51)) (* x100 x56)) (* x101 x61))) x126))) (>= x127 (+ (+ (+ (+ (+ (+ (* x77 x37) (* x78 x42)) (* x79 x47)) (* x80 x52)) (* x81 x57)) (+ (+ (+ (+ (* x102 x37) (* x103 x42)) (* x104 x47)) (* x105 x52)) (* x106 x57))) x127))) (>= x128 (+ (+ (+ (+ (+ (+ (* x77 x38) (* x78 x43)) (* x79 x48)) (* x80 x53)) (* x81 x58)) (+ (+ (+ (+ (* x102 x38) (* x103 x43)) (* x104 x48)) (* x105 x53)) (* x106 x58))) x128))) (>= x129 (+ (+ (+ (+ (+ (+ (* x77 x39) (* x78 x44)) (* x79 x49)) (* x80 x54)) (* x81 x59)) (+ (+ (+ (+ (* x102 x39) (* x103 x44)) (* x104 x49)) (* x105 x54)) (* x106 x59))) x129))) (>= x130 (+ (+ (+ (+ (+ (+ (* x77 x40) (* x78 x45)) (* x79 x50)) (* x80 x55)) (* x81 x60)) (+ (+ (+ (+ (* x102 x40) (* x103 x45)) (* x104 x50)) (* x105 x55)) (* x106 x60))) x130))) (>= x131 (+ (+ (+ (+ (+ (+ (* x77 x41) (* x78 x46)) (* x79 x51)) (* x80 x56)) (* x81 x61)) (+ (+ (+ (+ (* x102 x41) (* x103 x46)) (* x104 x51)) (* x105 x56)) (* x106 x61))) x131))) (>= x132 (+ (+ (+ (+ (+ (+ (* x82 x37) (* x83 x42)) (* x84 x47)) (* x85 x52)) (* x86 x57)) (+ (+ (+ (+ (* x107 x37) (* x108 x42)) (* x109 x47)) (* x110 x52)) (* x111 x57))) x132))) (>= x133 (+ (+ (+ (+ (+ (+ (* x82 x38) (* x83 x43)) (* x84 x48)) (* x85 x53)) (* x86 x58)) (+ (+ (+ (+ (* x107 x38) (* x108 x43)) (* x109 x48)) (* x110 x53)) (* x111 x58))) x133))) (>= x134 (+ (+ (+ (+ (+ (+ (* x82 x39) (* x83 x44)) (* x84 x49)) (* x85 x54)) (* x86 x59)) (+ (+ (+ (+ (* x107 x39) (* x108 x44)) (* x109 x49)) (* x110 x54)) (* x111 x59))) x134))) (>= x135 (+ (+ (+ (+ (+ (+ (* x82 x40) (* x83 x45)) (* x84 x50)) (* x85 x55)) (* x86 x60)) (+ (+ (+ (+ (* x107 x40) (* x108 x45)) (* x109 x50)) (* x110 x55)) (* x111 x60))) x135))) (>= x136 (+ (+ (+ (+ (+ (+ (* x82 x41) (* x83 x46)) (* x84 x51)) (* x85 x56)) (* x86 x61)) (+ (+ (+ (+ (* x107 x41) (* x108 x46)) (* x109 x51)) (* x110 x56)) (* x111 x61))) x136))) (>= x137 (+ (+ (+ (+ (+ (+ (* x87 x37) (* x88 x42)) (* x89 x47)) (* x90 x52)) (* x91 x57)) (+ (+ (+ (+ (* x112 x37) (* x113 x42)) (* x114 x47)) (* x115 x52)) (* x116 x57))) x137))) (>= x138 (+ (+ (+ (+ (+ (+ (* x87 x38) (* x88 x43)) (* x89 x48)) (* x90 x53)) (* x91 x58)) (+ (+ (+ (+ (* x112 x38) (* x113 x43)) (* x114 x48)) (* x115 x53)) (* x116 x58))) x138))) (>= x139 (+ (+ (+ (+ (+ (+ (* x87 x39) (* x88 x44)) (* x89 x49)) (* x90 x54)) (* x91 x59)) (+ (+ (+ (+ (* x112 x39) (* x113 x44)) (* x114 x49)) (* x115 x54)) (* x116 x59))) x139))) (>= x140 (+ (+ (+ (+ (+ (+ (* x87 x40) (* x88 x45)) (* x89 x50)) (* x90 x55)) (* x91 x60)) (+ (+ (+ (+ (* x112 x40) (* x113 x45)) (* x114 x50)) (* x115 x55)) (* x116 x60))) x140))) (>= x141 (+ (+ (+ (+ (+ (+ (* x87 x41) (* x88 x46)) (* x89 x51)) (* x90 x56)) (* x91 x61)) (+ (+ (+ (+ (* x112 x41) (* x113 x46)) (* x114 x51)) (* x115 x56)) (* x116 x61))) x141))))) (and (> ?v_4 x6) (and (and (and (and (>= ?v_4 x6) (>= (+ x33 (+ (+ (+ (+ (* x42 x6) (* x43 x7)) (* x44 x8)) (* x45 x9)) (* x46 x10))) x7)) (>= (+ x34 (+ (+ (+ (+ (* x47 x6) (* x48 x7)) (* x49 x8)) (* x50 x9)) (* x51 x10))) x8)) (>= (+ x35 (+ (+ (+ (+ (* x52 x6) (* x53 x7)) (* x54 x8)) (* x55 x9)) (* x56 x10))) x9)) (>= (+ x36 (+ (+ (+ (+ (* x57 x6) (* x58 x7)) (* x59 x8)) (* x60 x9)) (* x61 x10))) x10)))) (and (and (> ?v_5 0) (and (and (and (and (>= ?v_5 0) (>= (+ x33 (+ (+ (+ (+ (* x42 x142) (* x43 x143)) (* x44 x144)) (* x45 x145)) (* x46 x146))) 0)) (>= (+ x34 (+ (+ (+ (+ (* x47 x142) (* x48 x143)) (* x49 x144)) (* x50 x145)) (* x51 x146))) 0)) (>= (+ x35 (+ (+ (+ (+ (* x52 x142) (* x53 x143)) (* x54 x144)) (* x55 x145)) (* x56 x146))) 0)) (>= (+ x36 (+ (+ (+ (+ (* x57 x142) (* x58 x143)) (* x59 x144)) (* x60 x145)) (* x61 x146))) 0))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (+ (+ (+ (+ (* x37 x172) (* x38 x177)) (* x39 x182)) (* x40 x187)) (* x41 x192)) 1) (>= (+ (+ (+ (+ (* x37 x173) (* x38 x178)) (* x39 x183)) (* x40 x188)) (* x41 x193)) 0)) (>= (+ (+ (+ (+ (* x37 x174) (* x38 x179)) (* x39 x184)) (* x40 x189)) (* x41 x194)) 0)) (>= (+ (+ (+ (+ (* x37 x175) (* x38 x180)) (* x39 x185)) (* x40 x190)) (* x41 x195)) 0)) (>= (+ (+ (+ (+ (* x37 x176) (* x38 x181)) (* x39 x186)) (* x40 x191)) (* x41 x196)) 0)) (>= (+ (+ (+ (+ (* x42 x172) (* x43 x177)) (* x44 x182)) (* x45 x187)) (* x46 x192)) 0)) (>= (+ (+ (+ (+ (* x42 x173) (* x43 x178)) (* x44 x183)) (* x45 x188)) (* x46 x193)) 1)) (>= (+ (+ (+ (+ (* x42 x174) (* x43 x179)) (* x44 x184)) (* x45 x189)) (* x46 x194)) 0)) (>= (+ (+ (+ (+ (* x42 x175) (* x43 x180)) (* x44 x185)) (* x45 x190)) (* x46 x195)) 0)) (>= (+ (+ (+ (+ (* x42 x176) (* x43 x181)) (* x44 x186)) (* x45 x191)) (* x46 x196)) 0)) (>= (+ (+ (+ (+ (* x47 x172) (* x48 x177)) (* x49 x182)) (* x50 x187)) (* x51 x192)) 0)) (>= (+ (+ (+ (+ (* x47 x173) (* x48 x178)) (* x49 x183)) (* x50 x188)) (* x51 x193)) 0)) (>= (+ (+ (+ (+ (* x47 x174) (* x48 x179)) (* x49 x184)) (* x50 x189)) (* x51 x194)) 1)) (>= (+ (+ (+ (+ (* x47 x175) (* x48 x180)) (* x49 x185)) (* x50 x190)) (* x51 x195)) 0)) (>= (+ (+ (+ (+ (* x47 x176) (* x48 x181)) (* x49 x186)) (* x50 x191)) (* x51 x196)) 0)) (>= (+ (+ (+ (+ (* x52 x172) (* x53 x177)) (* x54 x182)) (* x55 x187)) (* x56 x192)) 0)) (>= (+ (+ (+ (+ (* x52 x173) (* x53 x178)) (* x54 x183)) (* x55 x188)) (* x56 x193)) 0)) (>= (+ (+ (+ (+ (* x52 x174) (* x53 x179)) (* x54 x184)) (* x55 x189)) (* x56 x194)) 0)) (>= (+ (+ (+ (+ (* x52 x175) (* x53 x180)) (* x54 x185)) (* x55 x190)) (* x56 x195)) 1)) (>= (+ (+ (+ (+ (* x52 x176) (* x53 x181)) (* x54 x186)) (* x55 x191)) (* x56 x196)) 0)) (>= (+ (+ (+ (+ (* x57 x172) (* x58 x177)) (* x59 x182)) (* x60 x187)) (* x61 x192)) 0)) (>= (+ (+ (+ (+ (* x57 x173) (* x58 x178)) (* x59 x183)) (* x60 x188)) (* x61 x193)) 0)) (>= (+ (+ (+ (+ (* x57 x174) (* x58 x179)) (* x59 x184)) (* x60 x189)) (* x61 x194)) 0)) (>= (+ (+ (+ (+ (* x57 x175) (* x58 x180)) (* x59 x185)) (* x60 x190)) (* x61 x195)) 0)) (>= (+ (+ (+ (+ (* x57 x176) (* x58 x181)) (* x59 x186)) (* x60 x191)) (* x61 x196)) 1)))) ?v_6))))
(check-sat)
(exit)
