(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* skoX (+ 120000000000000000000. (* skoX (* skoX 120000.))))) 0.)) (and (not (<= (* skoX (* skoX (+ 3600000000000000000000000. (* skoX (* skoX 3600000000.))))) 0.)) (and (<= 100. skoX) (and (<= skoX 120.) (and (<= (* pi (/ 1. 4.)) skoY) (and (<= skoY (* pi (/ 1. 3.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))))
(set-info :status sat)
(check-sat)
