(set-logic QF_NRA)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (* (- 1) (* skoB skoS)) 0) (and (= (+ (* skoS skoS) (* (- 1) (* skoA skoA)) (* (- 1) (* skoB skoB)) (* (- 1) (* skoB skoB skoA skoA))) 1) (and (not (<= skoS 0)) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))
(set-info :status sat)
(check-sat)
