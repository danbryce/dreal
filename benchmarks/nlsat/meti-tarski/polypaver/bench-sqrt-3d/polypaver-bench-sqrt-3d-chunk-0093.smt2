(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (* skoY (- 1.))) 0.)) (or (not (<= skoX 1.)) (or (not (<= skoY 1.)) (not (<= skoZ 1.))))))
(set-info :status sat)
(check-sat)
