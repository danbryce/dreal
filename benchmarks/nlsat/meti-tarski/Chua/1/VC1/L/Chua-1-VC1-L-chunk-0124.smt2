(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 13608.) 390625.) (* skoX (+ (/ 5103. 1220703125.) (* skoX (+ (/ (- 5103.) 15258789062500.) (* skoX (+ (/ 107163. 6103515625000000000.) (* skoX (+ (/ (- 45927.) 76293945312500000000000.) (* skoX (/ 45927. 3814697265625000000000000000.)))))))))))) (/ (- 18144.) 125.)) (and (not (<= skoX 0.)) (and (not (<= (* skoC (/ 1770. 689.)) skoS)) (and (<= skoS (* skoC (/ 1770. 689.))) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (<= skoX 0.)) (and (or (<= skoS (* skoC (/ 1770. 689.))) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))))
(set-info :status unsat)
(check-sat)
