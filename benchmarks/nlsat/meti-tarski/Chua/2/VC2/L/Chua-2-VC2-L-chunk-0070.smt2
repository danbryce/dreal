(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 16704.) 25.) (* skoX (+ (/ (- 30276.) 15625.) (* skoX (+ (/ (- 73167.) 19531250.) (* skoX (+ (/ (- 14852901.) 3125000000000.) (* skoX (+ (/ (- 61533447.) 15625000000000000.) (* skoX (/ (- 594823321.) 312500000000000000000.)))))))))))) (+ (+ 115200. (* skoC (- 87552.))) (* skoS 17280.)))) (and (not (<= (* skoX (+ (/ 8352. 625.) (* skoX (+ (/ 15138. 390625.) (* skoX (+ (/ 73167. 976562500.) (* skoX (+ (/ 14852901. 156250000000000.) (* skoX (+ (/ 61533447. 781250000000000000.) (* skoX (/ 594823321. 15625000000000000000000.)))))))))))) (- 2304.))) (and (<= skoX 0.) (and (<= skoS (* skoC (/ 76. 15.))) (and (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)

