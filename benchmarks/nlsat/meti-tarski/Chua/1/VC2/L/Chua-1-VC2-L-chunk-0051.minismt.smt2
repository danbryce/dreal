(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* (- 162421875000000000000000000) skoX) (* 19490625000000000000000 (* skoX skoX)) (* (- 1559250000000000000) (* skoX skoX skoX)) (* 81860625000000 (* skoX skoX skoX skoX)) (* (- 2806650000) (* skoX skoX skoX skoX skoX)) (* 56133 (* skoX skoX skoX skoX skoX skoX))) (- 676757812500000000000000000000)) (and (not (<= skoX 0)) (and (<= (+ (* (- 3) skoC) (* 13 skoS)) 0) (and (or (not (<= (+ (* 3 skoC) (* (- 13) skoS)) 0)) (not (<= (+ (* (- 3) skoC) (* 13 skoS)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status unsat)
(check-sat)
