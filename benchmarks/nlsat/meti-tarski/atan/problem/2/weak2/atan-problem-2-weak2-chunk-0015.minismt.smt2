(set-logic QF_NRA)
(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(assert (and (= (+ (* skoT skoT) (* skoB skoB)) 0) (and (not (<= skoT 0)) (and (not (<= (+ skoB skoA) 0)) (and (not (<= skoT 1)) (not (<= (+ skoB (* (- 1) skoA)) 0)))))))
(set-info :status unsat)
(check-sat)
