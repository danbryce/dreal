(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (- 1.))) (* skoB skoB))) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA))))))
(set-info :status unsat)
(check-sat)
