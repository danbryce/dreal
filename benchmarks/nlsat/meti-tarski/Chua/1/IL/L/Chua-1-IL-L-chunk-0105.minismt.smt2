(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* 2109375000000000000000000 skoX) (* (- 253125000000000000000) (* skoX skoX)) (* 20250000000000000 (* skoX skoX skoX)) (* (- 1063125000000) (* skoX skoX skoX skoX)) (* 36450000 (* skoX skoX skoX skoX skoX)) (* (- 729) (* skoX skoX skoX skoX skoX skoX))) 8789062500000000000000000000)) (and (not (<= skoX 0)) (not (<= (+ (* 235 skoC) (* 42 skoS)) 0)))))
(set-info :status unsat)
(check-sat)
