(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (+ (/ (- 1.) 24.) (* skoSQ3 (* skoSQ3 (/ 1. 24.)))))) (* skoX (* skoX (/ 1. 720.)))))))) 0.)) (and (not (<= skoSQ3 0.)) (and (not (<= skoX 0.)) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (+ (/ (- 1.) 10000000.) (* pi (/ 1. 2.))) skoX))))))))
(set-info :status sat)
(check-sat)
