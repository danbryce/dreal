(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (+ (* pi (/ 29906716275507200. 3119868895908289175433.)) (* skoY (* pi (/ (- 27950364949490226519206789120000.) 9733581927656007318022218939278759050737489.))))) (* pi (- 10.))) (and (= (* skoY skoY) (+ 277555600. (* (/ 265. 128.) (* (/ 265. 128.) (+ 15328072984. (* (/ 265. 128.) (* (/ 265. 128.) (+ 129098541721. (* (/ 265. 128.) (* (/ 265. 128.) (+ 21404723599. (* (/ 265. 128.) (* (/ 265. 128.) (+ 1024027285. (* (/ 265. 128.) (* (/ 265. 128.) 15132100.)))))))))))))))) (and (= (* skoY skoY) (+ 277555600. (* skoX (* skoX (+ 15328072984. (* skoX (* skoX (+ 129098541721. (* skoX (* skoX (+ 21404723599. (* skoX (* skoX (+ 1024027285. (* skoX (* skoX 15132100.)))))))))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (<= 0. skoY)))))))
(set-info :status unsat)
(check-sat)
