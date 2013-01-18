(set-logic QF_NRA)

(declare-fun pi () Real)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(assert (and (<= (+ (/ (- 1.) 10000000.) (* pi (/ 1. 2.))) skoX) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= skoSQ3 0.)))))))
(set-info :status sat)
(check-sat)
