(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= 0. skoT)) (and (not (<= (* skoT (* skoT (+ (+ (* skoA skoA) (* skoB skoB)) (* skoT skoT)))) (* skoB (* skoB (* skoA (* skoA (- 1.))))))) (and (not (= skoT 0.)) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status sat)
(check-sat)
