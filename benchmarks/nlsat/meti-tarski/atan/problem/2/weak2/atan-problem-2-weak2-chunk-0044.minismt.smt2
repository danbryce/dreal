(set-logic QF_NRA)
(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (+ (* (- 1) (* skoB skoT skoT)) (* (- 1) (* skoB skoB skoB))) 0)) (and (not (<= (+ skoB skoA) 0)) (and (not (<= skoT 1)) (not (<= (+ skoB (* (- 1) skoA)) 0))))))
(set-info :status unsat)
(check-sat)
