(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* (- 1) skoA) 0)) (and (not (<= (+ (* 157 (* skoT skoB skoB skoA)) (* 157 (* skoT skoT skoT skoA)) (* 100 (* skoT skoT skoA skoA)) (* 100 (* skoT skoT skoB skoB)) (* 100 (* skoT skoT skoT skoT)) (* 100 (* skoB skoB skoB skoA)) (* 30 (* skoT skoT skoB skoB skoA)) (* 30 (* skoT skoT skoT skoT skoA))) 0)) (and (not (<= (+ (* skoT skoB skoB) (* skoT skoT skoT)) 0)) (and (not (<= (+ skoB skoA) 0)) (and (not (<= skoT 1)) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))
(set-info :status sat)
(check-sat)
