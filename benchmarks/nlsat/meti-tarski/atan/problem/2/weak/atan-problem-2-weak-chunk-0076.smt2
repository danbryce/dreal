(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoT (* skoT (+ (+ (* skoA (- 1.)) skoB) (* skoS (- 1.))))) (* skoS (+ (* skoA (- 1.)) skoB))) (and (not (<= (* skoT (* skoS (- 1.))) 0.)) (and (not (<= skoT 0.)) (and (not (= skoT 0.)) (and (or (not (<= (- 1.) skoT)) (<= 0. skoT)) (and (or (not (<= 0. skoT)) (not (<= skoT 1.))) (and (= (* skoT (* skoT (+ (+ (* skoA (* skoA (- 1.))) (* skoB (* skoB (- 1.)))) (* skoT (* skoT (- 1.)))))) (+ (* skoB (* skoB (* skoA skoA))) (* skoS (* skoS (- 1.))))) (and (<= 0. skoS) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))))))))
(set-info :status unsat)
(check-sat)
