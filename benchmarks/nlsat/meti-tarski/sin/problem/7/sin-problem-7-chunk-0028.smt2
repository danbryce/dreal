(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= skoY 0.) (and (not (<= (* skoY (+ 1. (* skoY (* skoY (/ (- 1.) 6.))))) 0.)) (and (not (<= skoY skoX)) (and (<= 0. skoX) (and (<= skoY (* pi (/ 1. 2.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.))))))))))
(set-info :status unsat)
(check-sat)
