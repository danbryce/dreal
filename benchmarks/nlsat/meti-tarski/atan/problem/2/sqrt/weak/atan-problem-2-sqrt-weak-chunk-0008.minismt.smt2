(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (+ (* skoT skoT skoA skoA) (* skoT skoT skoB skoB) (* skoT skoT skoT skoT) (* skoB skoB skoA skoA)) 0)) (and (not (<= (* 2 skoT) 3)) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0)))))))
(set-info :status sat)
(check-sat)
