(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (+ (/ 2990671627550720. 3119868895908289175433.) (* skoY (+ (/ 1118014597979609060768271564800. 1081509103072889702002468771030973227859721.) (* skoY (+ (/ 1671807268682570670995559446312277222883328000. 10122499833956341531490039777630369712442039565143498231450302579.) (* skoY (/ 312489160323876717136102299938039485656788843320060149760000. 94742617142391635278791968904900383720022818743270331343654778954576407966594790025121.)))))))) 0.) (and (= (* skoY skoY) (+ 277555600. (* (/ 265. 128.) (* (/ 265. 128.) (+ 15328072984. (* (/ 265. 128.) (* (/ 265. 128.) (+ 129098541721. (* (/ 265. 128.) (* (/ 265. 128.) (+ 21404723599. (* (/ 265. 128.) (* (/ 265. 128.) (+ 1024027285. (* (/ 265. 128.) (* (/ 265. 128.) 15132100.)))))))))))))))) (and (= (* skoY skoY) (+ 277555600. (* skoX (* skoX (+ 15328072984. (* skoX (* skoX (+ 129098541721. (* skoX (* skoX (+ 21404723599. (* skoX (* skoX (+ 1024027285. (* skoX (* skoX 15132100.)))))))))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (<= 0. skoY)))))))
(set-info :status unsat)
(check-sat)
