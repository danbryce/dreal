(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(declare-fun skoB () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* 157 (* skoT skoA skoS)) (* 100 (* skoT skoT skoS)) (* 100 (* skoA skoB skoS)) (* 100 (* skoT skoT skoA skoA)) (* 100 (* skoT skoT skoA skoS)) (* (- 100) (* skoT skoT skoA skoB))) 0) (and (not (<= skoT 0)) (and (or (<= (+ (* (- 1) skoT) skoB) 0) (<= skoT 0)) (and (or (not (<= (* (- 1) skoT) 1)) (<= (* (- 1) skoT) 0)) (and (or (not (<= (* (- 1) skoT) 0)) (not (<= skoT 1))) (and (= (+ (* skoS skoS) (* (- 1) (* skoT skoT skoA skoA)) (* (- 1) (* skoT skoT skoB skoB)) (* (- 1) (* skoT skoT skoT skoT)) (* (- 1) (* skoA skoA skoB skoB))) 0) (and (<= (* (- 1) skoS) 0) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ (* (- 1) skoA) skoB) 0))))))))))))
(set-info :status unsat)
(check-sat)
