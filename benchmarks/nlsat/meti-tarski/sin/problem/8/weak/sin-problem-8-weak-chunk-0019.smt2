(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (+ 1. (* skoY (* skoY (/ (- 1.) 6.))))) 0.)) (and (not (<= skoY skoX)) (and (not (<= skoX 0.)) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (+ (/ (- 1.) 2000.) (* pi (/ 1. 2.))) skoY))))))))
(set-info :status sat)
(check-sat)
