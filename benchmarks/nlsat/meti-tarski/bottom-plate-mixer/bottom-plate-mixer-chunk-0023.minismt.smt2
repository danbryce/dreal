(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoCB () Real)
(declare-fun skoSB () Real)
(assert (and (<= (* (- 366500000) skoX) (- 177)) (and (<= (+ (* (- 7383) skoS) (* (- 3400) skoC)) (- 760000)) (and (<= (+ (* 7383 skoS) (* 3400 skoC)) 760000) (and (<= (* 366500000 skoX) 177) (and (not (<= (+ (* 52000 skoS) (* 11400 skoC) (* 196 skoCB) (* 260 skoSB)) 63475)) (and (<= (* 10000000 skoX) 1) (<= (* (- 1) skoX) 0))))))))
(set-info :status unsat)
(check-sat)
