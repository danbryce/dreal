(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (<= (+ (* 3 skoS3) skoSX) 0) (and (not (<= skoX 1)) (and (= (+ (* (- 80) (* skoX skoX)) (* skoSX skoSX)) 75) (and (= (* skoS3 skoS3) 3) (and (not (<= skoX 0)) (and (not (<= skoSX 0)) (not (<= skoS3 0)))))))))
(set-info :status unsat)
(check-sat)
