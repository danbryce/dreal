(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (+ (/ 43697163269238834702067824395241620091610776759118139350505303843654936013114796670662198951936. 19708317705563036631462656091625738641401586337438359785624745523729198598590531756034664554045605915.) (* pi (/ (- 4440960449936097280.) 508538630033051135595579.)))) (* pi (- 20.))) (and (<= 0. skoY) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (and (= (* skoY skoY) (+ 277555600. (* skoX (* skoX (+ 15328072984. (* skoX (* skoX (+ 129098541721. (* skoX (* skoX (+ 21404723599. (* skoX (* skoX (+ 1024027285. (* skoX (* skoX 15132100.)))))))))))))))) (= (* skoY skoY) (+ 277555600. (* (/ 265. 128.) (* (/ 265. 128.) (+ 15328072984. (* (/ 265. 128.) (* (/ 265. 128.) (+ 129098541721. (* (/ 265. 128.) (* (/ 265. 128.) (+ 21404723599. (* (/ 265. 128.) (* (/ 265. 128.) (+ 1024027285. (* (/ 265. 128.) (* (/ 265. 128.) 15132100.))))))))))))))))))))))
(set-info :status unsat)
(check-sat)
