(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 26502187500000000000000000000000000000000000000000000000000) skoX) (* 13289062500000000000000000000000000000000000000000000000000000 skoS) (* 74355468750000000000000000000000000000000000000000000000000000 skoC) (* 3180262500000000000000000000000000000000000000000000000 (* skoX skoX)) (* (- 254421000000000000000000000000000000000000000000000) (* skoX skoX skoX)) (* 15026740312500000000000000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 686936700000000000000000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 24901455375000000000000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 721283535000000000000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 16615281431250000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 298817464500000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 4018579695000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 37094581800000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 185472909 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 110425781250000000000000000000000000000000000000000000000000000)) (and (<= (+ (* (- 1746562500000000000000000000000000000000000000000000000000) skoX) (* 209587500000000000000000000000000000000000000000000000 (* skoX skoX)) (* (- 16767000000000000000000000000000000000000000000000) (* skoX skoX skoX)) (* 990300937500000000000000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 45270900000000000000000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 1641070125000000000000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 47534445000000000000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 1094989893750000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 19692841500000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 264834765000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 2444628600000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 12223143 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 7277343750000000000000000000000000000000000000000000000000000)) (and (<= (+ (* 1746562500000000000000000000000000000000000000000000000000 skoX) (* (- 209587500000000000000000000000000000000000000000000000) (* skoX skoX)) (* 16767000000000000000000000000000000000000000000000 (* skoX skoX skoX)) (* (- 990300937500000000000000000000000000000000000) (* skoX skoX skoX skoX)) (* 45270900000000000000000000000000000000000 (* skoX skoX skoX skoX skoX)) (* (- 1641070125000000000000000000000000000) (* skoX skoX skoX skoX skoX skoX)) (* 47534445000000000000000000000000 (* skoX skoX skoX skoX skoX skoX skoX)) (* (- 1094989893750000000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* 19692841500000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 264834765000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 2444628600000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 12223143) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 7277343750000000000000000000000000000000000000000000000000000) (and (not (<= skoX 0)) (and (<= (+ (* 42 skoS) (* 235 skoC)) 0) (and (or (not (<= (+ (* (- 42) skoS) (* (- 235) skoC)) 0)) (not (<= (+ (* 42 skoS) (* 235 skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))))
(set-info :status unsat)
(check-sat)
