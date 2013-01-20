(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun pi () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(assert (and (<= (* pi (/ 1. 2.)) skoS) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoS) (and (<= 0. skoCOSS) (<= skoSINS skoS)))))))
(set-info :status sat)
(check-sat)