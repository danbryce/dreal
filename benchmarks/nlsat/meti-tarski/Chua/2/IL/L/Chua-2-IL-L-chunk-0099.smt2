(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 8832.) 13.) (* skoX (+ (/ (- 3174.) 1625.) (* skoX (+ (/ (- 12167.) 3250000.) (* skoX (+ (/ (- 1958887.) 416000000000.) (* skoX (+ (/ (- 6436343.) 1664000000000000.) (* skoX (/ (- 148035889.) 79872000000000000000.)))))))))))) (+ (+ (/ 1536000. 13.) (* skoC (/ 331776. 65.))) (* skoS (/ (- 24301568724.) 203125.)))) (and (<= skoX 0.) (and (or (not (<= (* skoX (+ (+ (+ (/ (- 23.) 13.) (* skoC (/ 621. 8125.))) (* skoS (/ (- 46578006721.) 26000000000.))) (* skoX (+ (+ (/ (- 529.) 312000.) (* skoC (/ (- 4761.) 65000000.))) (* skoS (/ 1071294154583. 624000000000000.)))))) (+ (+ (/ 8000. 13.) (* skoC (/ 1728. 65.))) (* skoS (/ (- 2025130727.) 3250000.))))) (<= skoX 0.)) (and (<= (* skoC (/ 86400000. 2025130727.)) skoS) (and (or (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (not (<= skoS (* skoC (/ 86400000. 2025130727.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX)))))))))
(set-info :status sat)
(check-sat)
