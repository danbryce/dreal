(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoS () Real)
(declare-fun skoA () Real)
(assert (and (<= (+ (* 157 (* skoT skoB skoS)) (* (- 100) (* skoT skoT skoS)) (* (- 100) (* skoB skoS skoA)) (* 100 (* skoT skoT skoB skoA)) (* 10 (* skoT skoT skoB skoS)) (* (- 100) (* skoT skoT skoB skoB))) 0) (and (not (<= (* skoB skoS) 0)) (and (not (<= skoT 0)) (and (= (+ (* skoS skoS) (* (- 1) (* skoT skoT skoB skoB)) (* (- 1) (* skoT skoT skoA skoA)) (* (- 1) (* skoT skoT skoT skoT)) (* (- 1) (* skoB skoB skoA skoA))) 0) (and (<= (* (- 1) skoS) 0) (and (not (= skoT 0)) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0)))))))))))
(set-info :status sat)
(check-sat)
