(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* (- 54263808000000000000000) skoX) (* (- 156008448000000000000) (* skoX skoX)) (* (- 299016192000000000) (* skoX skoX skoX)) (* (- 376106304000000) (* skoX skoX skoX skoX)) (* (- 308944464000) (* skoX skoX skoX skoX skoX)) (* (- 148035889) (* skoX skoX skoX skoX skoX skoX))) 9437184000000000000000000) (and (not (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))
(set-info :status sat)
(check-sat)
