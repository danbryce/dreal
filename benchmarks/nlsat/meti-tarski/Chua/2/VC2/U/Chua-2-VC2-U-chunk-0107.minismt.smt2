(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 36288000000000000000000000000000000000) skoX) (* 508032000000000000000000000000000000 (* skoX skoX)) (* (- 4741632000000000000000000000000000) (* skoX skoX skoX)) (* 32672808000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 174254976000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 736953336000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 2490394032000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 6692933961000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 14043055236000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 22033069422000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 23727920916000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 13841287201 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 1270080000000000000000000000000000000000))) (and (not (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))
(set-info :status sat)
(check-sat)
