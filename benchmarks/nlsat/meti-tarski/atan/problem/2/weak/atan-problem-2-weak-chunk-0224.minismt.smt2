(set-logic QF_NRA)
(declare-fun skoA () Real)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(assert (and (not (<= (+ (* (- 1) (* skoA skoA)) (* (- 3) (* skoT skoT))) 0)) (and (or (not (<= (* (- 1) skoT) 0)) (not (<= skoT 1))) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ (* (- 1) skoA) skoB) 0)))))))
(set-info :status unsat)
(check-sat)
