(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoSQ3 (* skoSQ3 3.)) 0.) (and (<= (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (+ (/ (- 3.) 2.) (* skoSQ3 (* skoSQ3 (/ 1. 2.)))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (/ 1. 12.))) (* skoX (* skoX (+ (+ (/ 1. 720.) (* skoSQ3 (* skoSQ3 (/ (- 1.) 240.)))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (/ 1. 13440.))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (/ (- 1.) 1209600.))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (/ 1. 159667200.))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (/ (- 1.) 29059430400.))) (* skoX (* skoX (* skoSQ3 (* skoSQ3 (/ 1. 6974263296000.)))))))))))))))))))))))))) (* skoSQ3 (* skoSQ3 (+ (- 3.) (* skoSQ3 (* skoSQ3 (+ (- 2.) (* skoSQ3 skoSQ3)))))))) (and (not (<= skoSQ3 0.)) (and (not (<= skoX 0.)) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (+ (/ (- 1.) 10000000.) (* pi (/ 1. 2.))) skoX)) (= (* skoSQ3 skoSQ3) 3.)))))))))
(set-info :status unsat)
(check-sat)
