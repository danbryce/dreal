(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 46883930112. 390625.) (* skoX (+ (/ (- 17581473792.) 1220703125.) (* skoX (+ (/ 4395368448. 3814697265625.) (* skoX (+ (/ (- 811254528.) 11920928955078125.) (* skoX (+ (/ 115893504. 37252902984619140625.) (* skoX (+ (/ (- 13128561.) 116415321826934814453125.) (* skoX (+ (/ 9506889. 2910383045673370361328125000.) (* skoX (+ (/ (- 175198383.) 2328306436538696289062500000000000.) (* skoX (+ (/ 39385683. 29103830456733703613281250000000000000.) (* skoX (+ (/ (- 52966953.) 2910383045673370361328125000000000000000000.) (* skoX (+ (/ 12223143. 72759576141834259033203125000000000000000000000.) (* skoX (/ (- 12223143.) 14551915228366851806640625000000000000000000000000000.)))))))))))))))))))))))) (/ 62511906816. 125.)) (and (not (<= (* skoX (+ (/ (- 46883930112.) 390625.) (* skoX (+ (/ 17581473792. 1220703125.) (* skoX (+ (/ (- 4395368448.) 3814697265625.) (* skoX (+ (/ 811254528. 11920928955078125.) (* skoX (+ (/ (- 115893504.) 37252902984619140625.) (* skoX (+ (/ 13128561. 116415321826934814453125.) (* skoX (+ (/ (- 9506889.) 2910383045673370361328125000.) (* skoX (+ (/ 175198383. 2328306436538696289062500000000000.) (* skoX (+ (/ (- 39385683.) 29103830456733703613281250000000000000.) (* skoX (+ (/ 52966953. 2910383045673370361328125000000000000000000.) (* skoX (+ (/ (- 12223143.) 72759576141834259033203125000000000000000000000.) (* skoX (/ 12223143. 14551915228366851806640625000000000000000000000000000.)))))))))))))))))))))))) (/ (- 62511906816.) 125.))) (and (not (<= skoX 0.)) (and (<= skoS (* skoC (/ (- 235.) 42.))) (and (or (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (not (<= skoS (* skoC (/ (- 235.) 42.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status sat)
(check-sat)
