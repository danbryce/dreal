(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= skoY 0.) (and (not (<= 0. skoY)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))))))))))
(set-info :status unsat)
(check-sat)
