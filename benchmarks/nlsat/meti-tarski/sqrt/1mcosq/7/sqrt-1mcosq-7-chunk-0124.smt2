(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= skoY (* skoX 10.)) (and (not (<= (* skoX 10.) skoY)) (and (<= (* skoY (* skoY (+ (/ (- 1.) 2.) (* skoY (* skoY (+ (/ 1. 24.) (* skoY (* skoY (/ (- 1.) 720.))))))))) (- 1.)) (and (<= (* skoY (* skoY (/ (- 1.) 2.))) (- 1.)) (and (or (not (<= (* skoX 10.) skoY)) (or (not (<= skoY (* skoX 10.))) (<= skoY 0.))) (and (not (<= skoY skoX)) (and (<= (/ 1. 20.) skoX) (and (<= skoY (* pi (/ 1. 2.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))))))
(set-info :status sat)
(check-sat)
