(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 8352.) 625.) (* skoX (+ (/ (- 15138.) 390625.) (* skoX (+ (/ (- 73167.) 976562500.) (* skoX (+ (/ (- 14852901.) 156250000000000.) (* skoX (+ (/ (- 61533447.) 781250000000000000.) (* skoX (/ (- 594823321.) 15625000000000000000000.)))))))))))) 2304.) (and (<= skoX 0.) (and (or (not (<= (* skoX (+ (+ (+ (/ (- 667.) 5500.) (* skoC (/ 116. 825.))) (* skoS (/ (- 4263.) 27500.))) (* skoX (+ (+ (/ (- 19343.) 165000000.) (* skoC (/ (- 841.) 6187500.))) (* skoS (/ 41209. 275000000.)))))) (+ (+ (/ 460. 11.) (* skoC (/ 1600. 33.))) (* skoS (/ (- 588.) 11.))))) (<= skoX 0.)) (and (<= (* skoC (/ 400. 441.)) skoS) (and (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (or (not (<= 0. skoX)) (or (not (<= skoX (/ 1570. 21.))) (<= 0. skoS))) (and (or (not (<= 0. skoX)) (or (not (<= skoX (/ 1570. 21.))) (<= 0. skoC))) (and (<= skoX 75.) (<= 0. skoX)))))))))))
(set-info :status sat)
(check-sat)
