(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= (+ (* (- 1) (* skoT skoB skoB)) (* (- 1) (* skoT skoT skoT))) 0) (and (not (= skoA 0)) (and (or (not (<= (* (- 1) skoA) 0)) (or (not (<= (+ (* (- 157) (* skoT skoB skoB skoB)) (* (- 157) (* skoT skoT skoT skoB)) (* 200 (* skoT skoT skoB skoB)) (* 100 (* skoT skoT skoT skoT)) (* 100 (* skoB skoB skoB skoA)) (* (- 30) (* skoT skoT skoB skoB skoB)) (* (- 30) (* skoT skoT skoT skoT skoB))) 0)) (<= (+ (* (- 1) skoT) skoB) 0))) (and (not (<= (+ skoB skoA) 0)) (and (not (<= skoT 1)) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))
(set-info :status sat)
(check-sat)
