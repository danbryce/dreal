(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (- 1.))) (+ (* skoA (- 1.)) skoB))) (and (not (<= (* skoT (* skoT (+ (+ (* skoA (+ 1. (* skoA (* skoA (- 2.))))) (* skoB (+ (+ (- 1.) (* skoA (* skoA 2.))) (* skoB (+ (* skoA (+ (- 2.) (* skoA (+ 2. skoA)))) (* skoB (+ 2. (* skoA (* skoA (- 1.)))))))))) (* skoT (* skoT (+ (+ (* skoA (+ (- 2.) (* skoA (+ 2. skoA)))) (* skoB (+ (+ 2. (* skoA (* skoA (- 1.)))) (* skoB (+ (+ 2. skoA) (* skoB (- 1.))))))) (* skoT (* skoT (+ (+ 2. skoA) (* skoB (- 1.))))))))))) (* skoB (* skoB (+ (* skoA (* skoA (* skoA 2.))) (* skoB (* skoA (* skoA (- 2.))))))))) (and (not (<= skoT (/ 3. 2.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status unsat)
(check-sat)
