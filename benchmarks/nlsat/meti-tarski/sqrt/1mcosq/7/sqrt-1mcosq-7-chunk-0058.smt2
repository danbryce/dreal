(set-logic QF_NRA)

(declare-fun pi () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (= skoY 0.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 20.) skoX) (and (<= skoY (* pi (/ 1. 2.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))
(set-info :status sat)
(check-sat)
