(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ (- 3600060000000000000000000.) (* skoX (* skoX (- 3600060000.)))))) (* skoY (* skoY (+ (* skoX (* skoX (+ 1050005000000000000000000. (* skoX (* skoX 1050005000.))))) (* skoY (* skoY (* skoX (* skoX (+ (- 75000000000000000000000.) (* skoX (* skoX (- 75000000.)))))))))))))) (+ 970000000000000000000000000000. (* skoX (* skoX (+ (- 120000000000000000000.) (* skoX (* skoX (- 3600119999.))))))))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))
(set-info :status sat)
(check-sat)
