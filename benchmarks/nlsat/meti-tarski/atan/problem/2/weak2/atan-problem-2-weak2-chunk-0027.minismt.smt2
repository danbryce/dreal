(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= (+ (* (- 1) (* skoT skoB skoB)) (* (- 1) (* skoT skoT skoT))) 0) (and (not (= skoT 0)) (and (not (<= (+ skoB skoA) 0)) (and (not (<= skoT 1)) (not (<= (+ skoB (* (- 1) skoA)) 0)))))))
(set-info :status sat)
(check-sat)
