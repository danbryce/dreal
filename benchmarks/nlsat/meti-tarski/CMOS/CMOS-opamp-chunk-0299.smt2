(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoY (+ (+ 900000000000000000000000. (* skoX (* skoX 900000000.))) (* skoY (* skoY (+ (- 75000000000000000000000.) (* skoX (* skoX (- 75000000.))))))))) (+ 1800060000000000000000000. (* skoX (* skoX 1800060000.))))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))
(set-info :status sat)
(check-sat)
