(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (+ (/ 747667906887680. 1039956298636096391811.) (* skoY (+ (/ 1118014597979609060768271564800. 3244527309218669106007406313092919683579163.) (* skoY (/ 417951817170642667748889861578069305720832000. 30367499501869024594470119332891109137326118695430494694350907737.)))))) 0.) (and (= (* skoY skoY) (+ 277555600. (* (/ 265. 128.) (* (/ 265. 128.) (+ 15328072984. (* (/ 265. 128.) (* (/ 265. 128.) (+ 129098541721. (* (/ 265. 128.) (* (/ 265. 128.) (+ 21404723599. (* (/ 265. 128.) (* (/ 265. 128.) (+ 1024027285. (* (/ 265. 128.) (* (/ 265. 128.) 15132100.)))))))))))))))) (and (= (* skoY skoY) (+ 277555600. (* skoX (* skoX (+ 15328072984. (* skoX (* skoX (+ 129098541721. (* skoX (* skoX (+ 21404723599. (* skoX (* skoX (+ 1024027285. (* skoX (* skoX 15132100.)))))))))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (<= 0. skoY)))))))
(set-info :status unsat)
(check-sat)
