(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (not (<= (+ (* skoY skoY) (* (- 2) (* skoY skoA)) (* skoX skoX)) 0)))
(set-info :status sat)
(check-sat)