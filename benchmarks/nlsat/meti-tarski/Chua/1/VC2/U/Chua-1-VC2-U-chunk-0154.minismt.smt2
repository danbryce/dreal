(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 5847187500000000000000000000000000000000000000000000000000) skoX) (* 701662500000000000000000000000000000000000000000000000 (* skoX skoX)) (* (- 56133000000000000000000000000000000000000000000000) (* skoX skoX skoX)) (* 3315355312500000000000000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 151559100000000000000000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 5494017375000000000000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 159137055000000000000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 3665835731250000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 65928208500000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 886620735000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 8184191400000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 40920957 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 24363281250000000000000000000000000000000000000000000000000000))) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 3) skoC) (* 13 skoS)) 0)) (and (<= (+ (* 3 skoC) (* (- 13) skoS)) 0) (and (or (not (<= (+ (* (- 3) skoC) (* 13 skoS)) 0)) (<= skoX 0)) (and (or (<= (+ (* 3 skoC) (* (- 13) skoS)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))))
(set-info :status sat)
(check-sat)
