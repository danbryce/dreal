(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 208800000000000000000000) skoX) (* (- 605520000000000000000) (* skoX skoX)) (* (- 1170672000000000000) (* skoX skoX skoX)) (* (- 1485290100000000) (* skoX skoX skoX skoX)) (* (- 1230668940000) (* skoX skoX skoX skoX skoX)) (* (- 594823321) (* skoX skoX skoX skoX skoX skoX))) 36000000000000000000000000) (and (not (<= (+ (* (- 4802400000000000000000000) skoX) (* 1058400000000000000000000000 skoS) (* (- 960000000000000000000000000) skoC) (* (- 13926960000000000000000) (* skoX skoX)) (* (- 26925456000000000000) (* skoX skoX skoX)) (* (- 34161672300000000) (* skoX skoX skoX skoX)) (* (- 28305385620000) (* skoX skoX skoX skoX skoX)) (* (- 13680936383) (* skoX skoX skoX skoX skoX skoX))) 828000000000000000000000000)) (and (<= skoX 0) (and (or (not (<= (+ (* (- 300150000) skoX) (* 132300000000 skoS) (* (- 120000000000) skoC) (* (- 290145) (* skoX skoX)) (* (- 383670000) (* skoX skoS)) (* 348000000 (* skoX skoC)) (* 370881 (* skoX skoX skoS)) (* (- 336400) (* skoX skoX skoC))) 103500000000)) (<= skoX 0)) (and (<= (+ (* (- 441) skoS) (* 400 skoC)) 0) (and (or (not (<= (+ (* (- 441) skoS) (* 400 skoC)) 0)) (not (<= (+ (* 441 skoS) (* (- 400) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (or (not (<= (* (- 1) skoX) 0)) (or (not (<= (* 21 skoX) 1570)) (<= (* (- 1) skoS) 0))) (and (or (not (<= (* (- 1) skoX) 0)) (or (not (<= (* 21 skoX) 1570)) (<= (* (- 1) skoC) 0))) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))))))))
(set-info :status sat)
(check-sat)
