(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* 870000 skoX) (* 841 (* skoX skoX))) (- 300000000)) (and (<= (+ (* (- 300150000) skoX) (* 132300000000 skoS) (* (- 120000000000) skoC) (* (- 290145) (* skoX skoX)) (* (- 383670000) (* skoX skoS)) (* 348000000 (* skoX skoC)) (* 370881 (* skoX skoX skoS)) (* (- 336400) (* skoX skoX skoC))) 103500000000) (and (not (<= skoX 0)) (and (or (not (<= (+ (* (- 300150000) skoX) (* 132300000000 skoS) (* (- 120000000000) skoC) (* (- 290145) (* skoX skoX)) (* (- 383670000) (* skoX skoS)) (* 348000000 (* skoX skoC)) (* 370881 (* skoX skoX skoS)) (* (- 336400) (* skoX skoX skoC))) 103500000000)) (<= skoX 0)) (and (<= (+ (* (- 441) skoS) (* 400 skoC)) 0) (and (or (not (<= (+ (* (- 441) skoS) (* 400 skoC)) 0)) (not (<= (+ (* 441 skoS) (* (- 400) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (or (not (<= (* (- 1) skoX) 0)) (or (not (<= (* 21 skoX) 1570)) (<= (* (- 1) skoS) 0))) (and (or (not (<= (* (- 1) skoX) 0)) (or (not (<= (* 21 skoX) 1570)) (<= (* (- 1) skoC) 0))) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))))))))
(set-info :status unsat)
(check-sat)
