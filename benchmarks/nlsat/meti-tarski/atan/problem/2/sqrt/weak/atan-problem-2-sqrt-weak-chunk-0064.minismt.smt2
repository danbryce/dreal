(set-logic QF_NRA)
(declare-fun skoA () Real)
(declare-fun skoB () Real)
(declare-fun skoT () Real)
(assert (and (<= (+ (* (- 1) (* skoA skoA skoB skoT)) (* skoA skoB skoB skoT)) 0) (and (<= (+ (* (- 157) (* skoA skoB)) (* 50 (* skoA skoT)) (* (- 50) (* skoB skoT)) (* (- 50) (* skoA skoB skoT))) 0) (and (not (<= (+ (* 157 (* skoA skoB)) (* (- 50) (* skoA skoT)) (* 50 (* skoB skoT)) (* 50 (* skoA skoB skoT))) 0)) (and (not (<= (+ (* (- 1) skoA) skoB) 0)) (and (not (<= (* (- 1) skoB) (- 2))) (and (not (<= skoA 0)) (not (<= (* 2 skoT) 3)))))))))
(set-info :status unsat)
(check-sat)
