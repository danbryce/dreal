(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(assert (and (= (+ (* skoSINS skoSINS) (* skoCOSS skoCOSS)) 1) (and (<= (+ (* 24 skoS) (* (- 10) skoSINS) (* 12 skoCOSS) (* skoSINS skoSINS) (* 2 (* skoCOSS skoCOSS)) (* 24 (* skoS skoS)) (* (- 6) (* skoS skoSINS)) (* (- 2) (* skoSINS skoCOSS)) (* 24 (* skoS skoCOSS)) (* 8 (* skoS skoS skoS)) (* 6 (* skoS skoS skoSINS)) (* skoS skoSINS skoSINS) (* 2 (* skoS skoCOSS skoCOSS)) (* 12 (* skoS skoS skoCOSS)) (* 2 (* skoS skoS skoS skoSINS))) (- 8)) (<= (* (- 20) skoS) (- 9)))))
(set-info :status unsat)
(check-sat)
