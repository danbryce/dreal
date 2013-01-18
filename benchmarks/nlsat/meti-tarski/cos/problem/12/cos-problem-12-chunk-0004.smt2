(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoY skoY) (+ pi (* skoX (* skoX (- 1.))))) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi)))))
(set-info :status sat)
(check-sat)
