(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* 132890625000000000000000000 skoX) (* (- 15946875000000000000000) (* skoX skoX)) (* 1275750000000000000 (* skoX skoX skoX)) (* (- 66976875000000) (* skoX skoX skoX skoX)) (* 2296350000 (* skoX skoX skoX skoX skoX)) (* (- 45927) (* skoX skoX skoX skoX skoX skoX))) 553710937500000000000000000000) (and (<= skoX 0) (and (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0) (and (or (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (not (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))
(set-info :status sat)
(check-sat)
