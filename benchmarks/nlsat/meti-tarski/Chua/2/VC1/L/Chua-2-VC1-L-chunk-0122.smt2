(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ 400. 441.)) skoS)) (and (not (<= (* skoX (+ (/ (- 64032.) 1375.) (* skoX (+ (/ (- 116058.) 859375.) (* skoX (+ (/ (- 560947.) 2148437500.) (* skoX (+ (/ (- 113872241.) 343750000000000.) (* skoX (+ (/ (- 471756427.) 1718750000000000000.) (* skoX (/ (- 13680936383.) 103125000000000000000000.)))))))))))) (+ (+ (/ 88320. 11.) (* skoC (/ 102400. 11.))) (* skoS (/ (- 112896.) 11.))))) (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.))))))))
(set-info :status unsat)
(check-sat)
