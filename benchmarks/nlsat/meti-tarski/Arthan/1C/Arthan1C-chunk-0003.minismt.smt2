(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(assert (not (<= (+ (* (- 3) skoSINS) (* 2 skoCOSS) (* 6 (* skoS skoS)) (* (- 4) (* skoS skoSINS)) (* skoSINS skoSINS) (* (- 2) (* skoSINS skoCOSS)) (* 2 (* skoCOSS skoCOSS)) (* 10 (* skoS skoCOSS)) (* 2 (* skoS skoS skoS)) (* 2 (* skoS skoS skoSINS)) (* skoS skoSINS skoSINS) (* 2 (* skoS skoCOSS skoCOSS)) (* 6 (* skoS skoS skoCOSS)) (* skoS skoS skoS skoSINS)) 2)))
(set-info :status sat)
(check-sat)
