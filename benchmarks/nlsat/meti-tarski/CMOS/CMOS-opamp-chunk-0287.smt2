(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY (* skoY (* skoX (* skoX (+ (- 900000000000000000000000.) (* skoX (* skoX (- 900000000.)))))))) (* skoX (* skoX (+ (- 1800000000000000000000000.) (* skoX (* skoX (- 1800000000.))))))) (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 1800030000000000000000000.) (* skoX (* skoX (- 1800030000.)))))) (* skoY (* skoY (* skoX (* skoX (+ 450000000000000000000000. (* skoX (* skoX 450000000.)))))))))) (+ (/ 55289999999999882000000000000057. 114.) (* skoX (* skoX (+ (- 60000000000000000000.) (* skoX (* skoX (/ (- 3600119999.) 2.))))))))) (and (<= 100. skoX) (and (<= skoX 120.) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoY (* pi (/ 1. 3.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))))
(set-info :status unsat)
(check-sat)
