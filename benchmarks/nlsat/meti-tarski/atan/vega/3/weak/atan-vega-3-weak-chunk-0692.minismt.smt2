(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ skoY skoX skoZ (* (- 1) (* skoY skoX skoZ))) 0)) (and (not (<= skoY 1)) (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (* (- 1) skoX) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))
(set-info :status unsat)
(check-sat)
