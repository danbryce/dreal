(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= skoX 0.) (and (not (<= (* skoX (+ (/ (- 13608.) 390625.) (* skoX (+ (/ 5103. 1220703125.) (* skoX (+ (/ (- 5103.) 15258789062500.) (* skoX (+ (/ 107163. 6103515625000000000.) (* skoX (+ (/ (- 45927.) 76293945312500000000000.) (* skoX (/ 45927. 3814697265625000000000000000.)))))))))))) (/ (- 18144.) 125.))) (and (not (<= (* skoX (+ (/ 93312. 78125.) (* skoX (+ (/ (- 34992.) 244140625.) (* skoX (+ (/ 8748. 762939453125.) (* skoX (+ (/ (- 45927.) 76293945312500000.) (* skoX (+ (/ 19683. 953674316406250000000.) (* skoX (/ (- 19683.) 47683715820312500000000000.)))))))))))) (+ (+ (/ 124416. 25.) (* skoC (/ 101952. 25.))) (* skoS (/ (- 198432.) 125.))))) (and (<= (* skoC (/ 1770. 689.)) skoS) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (not (<= skoS (* skoC (/ 1770. 689.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
