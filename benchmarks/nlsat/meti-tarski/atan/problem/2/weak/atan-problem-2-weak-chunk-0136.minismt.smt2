(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* 157 (* skoT skoB skoS)) (* (- 100) (* skoT skoT skoS)) (* (- 100) (* skoB skoA skoS)) (* 100 (* skoT skoT skoB skoA)) (* 100 (* skoT skoT skoB skoS)) (* (- 100) (* skoT skoT skoB skoB))) 0)) (and (not (<= skoT 0)) (and (or (not (<= (* (- 1) skoT) 0)) (not (<= skoT 1))) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))
(set-info :status sat)
(check-sat)
