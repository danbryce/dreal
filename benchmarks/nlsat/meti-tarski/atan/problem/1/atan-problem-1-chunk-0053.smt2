(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (not (<= (* skoX (+ (+ (* skoS3 (- 15.)) (* skoSX 3.)) (* skoX (* skoX (* skoS3 (- 8.)))))) 0.)) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.))))))
(set-info :status sat)
(check-sat)
