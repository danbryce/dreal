(set-logic QF_NRA)
(declare-fun pi () Real)
(declare-fun skoA () Real)
(declare-fun skoX () Real)
(assert (and (= skoA 0) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ pi (* (- 2) skoA)) 0)) (and (not (<= skoX 0)) (not (<= (+ skoA (* (- 1) skoX)) 0))))))))
(set-info :status unsat)
(check-sat)
