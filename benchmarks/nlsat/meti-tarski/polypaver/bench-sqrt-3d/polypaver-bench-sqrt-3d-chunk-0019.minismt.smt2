(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (not (<= (* 2 (* skoX skoY skoZ)) (- 1))))
(set-info :status sat)
(check-sat)
