(set-logic QF_NRA)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* 3 skoS3) skoSX) 0)) (and (not (<= skoX 0)) (and (not (<= skoSX 0)) (not (<= skoS3 0))))))
(set-info :status sat)
(check-sat)
