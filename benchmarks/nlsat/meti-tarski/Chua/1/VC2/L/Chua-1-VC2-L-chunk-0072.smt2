(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 16307453952.) 3125.) (* skoX (+ (/ 6115295232. 9765625.) (* skoX (+ (/ (- 1528823808.) 30517578125.) (* skoX (+ (/ 282175488. 95367431640625.) (* skoX (+ (/ (- 40310784.) 298023223876953125.) (* skoX (+ (/ 4566456. 931322574615478515625.) (* skoX (+ (/ (- 413343.) 2910383045673370361328125.) (* skoX (+ (/ 7617321. 2328306436538696289062500000000.) (* skoX (+ (/ (- 1712421.) 29103830456733703613281250000000000.) (* skoX (+ (/ 2302911. 2910383045673370361328125000000000000000.) (* skoX (+ (/ (- 531441.) 72759576141834259033203125000000000000000000.) (* skoX (/ 531441. 14551915228366851806640625000000000000000000000000.)))))))))))))))))))))))) (- 21743271936.)) (and (not (<= skoX 0.)) (and (<= skoS (* skoC (/ 3. 13.))) (and (or (not (<= (* skoC (/ 3. 13.)) skoS)) (not (<= skoS (* skoC (/ 3. 13.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status unsat)
(check-sat)
