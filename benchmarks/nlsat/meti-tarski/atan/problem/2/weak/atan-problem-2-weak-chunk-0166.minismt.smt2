(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* 157 (* skoB skoA skoS)) (* 50 (* skoT skoB skoS)) (* (- 50) (* skoT skoA skoS)) (* 50 (* skoT skoB skoA skoA)) (* (- 50) (* skoT skoB skoB skoA)) (* 50 (* skoT skoB skoA skoS))) 0) (and (not (<= skoT 0)) (and (or (<= (+ (* (- 1) skoT) skoB) 0) (<= skoT 0)) (and (or (not (<= (* (- 1) skoT) 1)) (<= (* (- 1) skoT) 0)) (and (or (not (<= (* (- 1) skoT) 0)) (not (<= skoT 1))) (and (= (+ (* skoS skoS) (* (- 1) (* skoT skoT skoA skoA)) (* (- 1) (* skoT skoT skoB skoB)) (* (- 1) (* skoT skoT skoT skoT)) (* (- 1) (* skoB skoB skoA skoA))) 0) (and (<= (* (- 1) skoS) 0) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))))))
(set-info :status unsat)
(check-sat)
