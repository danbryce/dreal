(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ 128421199872. 390625.) (* skoX (+ (/ (- 48157949952.) 1220703125.) (* skoX (+ (/ 12039487488. 3814697265625.) (* skoX (+ (/ (- 2222131968.) 11920928955078125.) (* skoX (+ (/ 317447424. 37252902984619140625.) (* skoX (+ (/ (- 35960841.) 116415321826934814453125.) (* skoX (+ (/ 26040609. 2910383045673370361328125000.) (* skoX (+ (/ (- 479891223.) 2328306436538696289062500000000000.) (* skoX (+ (/ 107882523. 29103830456733703613281250000000000000.) (* skoX (+ (/ (- 145083393.) 2910383045673370361328125000000000000000000.) (* skoX (+ (/ 33480783. 72759576141834259033203125000000000000000000000.) (* skoX (/ (- 33480783.) 14551915228366851806640625000000000000000000000000000.)))))))))))))))))))))))) (/ 171228266496. 125.)) (and (not (<= skoX 0.)) (and (<= (* skoC (/ 1770. 689.)) skoS) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (not (<= skoS (* skoC (/ 1770. 689.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)
