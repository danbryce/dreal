(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (+ (/ 1. 2.) (* skoSQ3 (* skoSQ3 (/ (- 1.) 6.)))))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (+ (/ (- 1.) 24.) (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ 1. 72.)))))))) (* skoX (* skoX (+ (+ (/ 1. 720.) (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ (- 1.) 2160.)))))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ 1. 120960.))))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ (- 1.) 10886400.))))))) (* skoX (* skoX (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ 1. 1437004800.)))))))))))))))))))))))) (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (+ 3. (* skoSQ3 (* skoSQ3 (- 1.))))))))) (and (= (* skoSQ3 skoSQ3) 3.) (and (not (<= (+ (/ (- 1.) 10000000.) (* pi (/ 1. 2.))) skoX)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= skoSQ3 0.)))))))))
(set-info :status unsat)
(check-sat)
