(set-logic QF_NRA)
(declare-fun skoM () Real)
(declare-fun skoCOSS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoS () Real)
(assert (and (= (* skoM skoM) 0) (and (not (= skoM 0)) (and (= (+ (* skoSINS skoSINS) (* skoCOSS skoCOSS)) 1) (and (<= (* (- 1) skoS) (- 2)) (<= (* (- 1) skoM) (- 2)))))))
(set-info :status unsat)
(check-sat)
