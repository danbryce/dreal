(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoA (+ 1. (* skoA (* skoA (/ (- 1.) 6.))))) 0.)) (and (not (<= skoA skoX)) (and (not (<= skoX 0.)) (and (not (<= (* pi (/ 1. 2.)) skoA)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))
(set-info :status sat)
(check-sat)