(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= pi (/ 2944313118675309517893327913770056693331415133307224689027900572059989397946232. 3139139565556413757031246886608524785790584795902482097418859414134156981043185.)) (and (<= 0. skoY) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (and (= (* skoY skoY) (+ 277555600. (* skoX (* skoX (+ 15328072984. (* skoX (* skoX (+ 129098541721. (* skoX (* skoX (+ 21404723599. (* skoX (* skoX (+ 1024027285. (* skoX (* skoX 15132100.)))))))))))))))) (= (* skoY skoY) (+ 277555600. (* (/ 265. 128.) (* (/ 265. 128.) (+ 15328072984. (* (/ 265. 128.) (* (/ 265. 128.) (+ 129098541721. (* (/ 265. 128.) (* (/ 265. 128.) (+ 21404723599. (* (/ 265. 128.) (* (/ 265. 128.) (+ 1024027285. (* (/ 265. 128.) (* (/ 265. 128.) 15132100.))))))))))))))))))))))
(set-info :status unsat)
(check-sat)
