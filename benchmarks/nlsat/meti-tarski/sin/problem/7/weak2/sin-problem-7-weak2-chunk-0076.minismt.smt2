(set-logic QF_NRA)
(declare-fun skoA () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= skoA 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ (* (- 2) skoA) pi) 0)) (and (not (<= skoX 0)) (and (not (<= (+ skoA (* (- 1) skoX)) 0)) (or (not (<= (+ skoA (* (- 2000) skoX)) 0)) (not (<= (+ (* (- 1) skoA) (* 2000 skoX)) 0))))))))))
(set-info :status sat)
(check-sat)
