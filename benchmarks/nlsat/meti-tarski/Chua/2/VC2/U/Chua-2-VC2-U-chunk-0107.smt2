(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ (- 152202903552.) 5.) (* skoX (+ (/ 266355081216. 625.) (* skoX (+ (/ (- 310747594752.) 78125.) (* skoX (+ (/ 267655643136. 9765625.) (* skoX (+ (/ (- 178437095424.) 1220703125.) (* skoX (+ (/ 94330027008. 152587890625.) (* skoX (+ (/ (- 39846304512.) 19073486328125.) (* skoX (+ (/ 13385867922. 2384185791015625.) (* skoX (+ (/ (- 3510763809.) 298023223876953125.) (* skoX (+ (/ 11016534711. 596046447753906250000.) (* skoX (+ (/ (- 5931980229.) 298023223876953125000000.) (* skoX (/ 13841287201. 1192092895507812500000000000.)))))))))))))))))))))))) (- 1065420324864.))) (and (not (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status sat)
(check-sat)
