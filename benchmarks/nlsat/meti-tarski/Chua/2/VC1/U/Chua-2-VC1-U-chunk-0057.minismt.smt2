(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 15750000000000000) skoX) (* 220500000000000 (* skoX skoX)) (* (- 2058000000000) (* skoX skoX skoX)) (* 12605250000 (* skoX skoX skoX skoX)) (* (- 50421000) (* skoX skoX skoX skoX skoX)) (* 117649 (* skoX skoX skoX skoX skoX skoX))) (- 540225000000000000))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))
(set-info :status sat)
(check-sat)
