(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (* skoX (* skoX (+ 1800000000000000000000000. (* skoX (* skoX 1800000000.))))) (* skoY (* skoY (* skoX (* skoX (+ (- 150000000000000000000000.) (* skoX (* skoX (- 150000000.))))))))))) (* skoX (* skoX (+ 3600000000000000000000000. (* skoX (* skoX 3600000000.))))))) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi)))))
(set-info :status sat)
(check-sat)
