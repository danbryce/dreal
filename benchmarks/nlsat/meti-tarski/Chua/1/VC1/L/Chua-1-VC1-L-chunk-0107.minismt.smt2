(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 2109375000000000000000000) skoX) (* 253125000000000000000 (* skoX skoX)) (* (- 20250000000000000) (* skoX skoX skoX)) (* 1063125000000 (* skoX skoX skoX skoX)) (* (- 36450000) (* skoX skoX skoX skoX skoX)) (* 729 (* skoX skoX skoX skoX skoX skoX))) (- 8789062500000000000000000000)) (and (<= skoX 0) (and (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (and (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (and (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0) (and (or (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (<= skoX 0)) (and (or (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0)))))))))))
(set-info :status unsat)
(check-sat)
