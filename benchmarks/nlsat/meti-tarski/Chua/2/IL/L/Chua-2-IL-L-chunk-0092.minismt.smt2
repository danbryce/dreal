(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 54263808000000000000000) skoX) (* 9555765647376384000000000 skoS) (* (- 407686348800000000000000) skoC) (* (- 156008448000000000000) (* skoX skoX)) (* (- 299016192000000000) (* skoX skoX skoX)) (* (- 376106304000000) (* skoX skoX skoX skoX)) (* (- 308944464000) (* skoX skoX skoX skoX skoX)) (* (- 148035889) (* skoX skoX skoX skoX skoX skoX))) 9437184000000000000000000)) (and (not (<= (+ (* 54263808000000000000000 skoX) (* 156008448000000000000 (* skoX skoX)) (* 299016192000000000 (* skoX skoX skoX)) (* 376106304000000 (* skoX skoX skoX skoX)) (* 308944464000 (* skoX skoX skoX skoX skoX)) (* 148035889 (* skoX skoX skoX skoX skoX skoX))) (- 9437184000000000000000000))) (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0))))))
(set-info :status sat)
(check-sat)
