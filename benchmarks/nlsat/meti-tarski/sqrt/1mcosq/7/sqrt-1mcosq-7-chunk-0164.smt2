(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoX (* skoX (/ 1. 2.))) 1.) (and (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (+ (/ 1. 3628800.) (* skoY (* skoY (+ (/ (- 1.) 479001600.) (* skoY (* skoY (+ (/ 1. 87178291200.) (* skoY (* skoY (/ (- 1.) 20922789888000.)))))))))))))))))))))))) 1.) (and (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (+ (/ (- 1.) 720.) (* skoY (* skoY (+ (/ 1. 40320.) (* skoY (* skoY (+ (/ (- 1.) 3628800.) (* skoY (* skoY (+ (/ 1. 479001600.) (* skoY (* skoY (/ (- 1.) 87178291200.))))))))))))))))))))) (- 1.)) (and (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (+ (/ 1. 3628800.) (* skoY (* skoY (/ (- 1.) 479001600.)))))))))))))))))) 1.) (and (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (+ (/ (- 1.) 720.) (* skoY (* skoY (+ (/ 1. 40320.) (* skoY (* skoY (/ (- 1.) 3628800.))))))))))))))) (- 1.)) (and (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (/ (- 1.) 720.))))))))) (- 1.)) (and (<= (* skoY (* skoY (/ (- 1.) 2.))) (- 1.)) (and (or (not (<= (* skoX 10.) skoY)) (or (not (<= skoY (* skoX 10.))) (<= skoY 0.))) (and (not (<= skoY skoX)) (and (<= (/ 1. 20.) skoX) (and (<= skoY (* pi (/ 1. 2.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))))))))))
(set-info :status sat)
(check-sat)
