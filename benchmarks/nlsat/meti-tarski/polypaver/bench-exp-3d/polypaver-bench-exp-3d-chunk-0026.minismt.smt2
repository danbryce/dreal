(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (not (<= (+ skoY skoX skoZ) 3)))
(set-info :status sat)
(check-sat)
