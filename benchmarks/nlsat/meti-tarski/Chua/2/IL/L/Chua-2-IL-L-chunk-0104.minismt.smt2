(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 54263808000000000000000) skoX) (* 9555765647376384000000000 skoS) (* (- 407686348800000000000000) skoC) (* (- 156008448000000000000) (* skoX skoX)) (* (- 299016192000000000) (* skoX skoX skoX)) (* (- 376106304000000) (* skoX skoX skoX skoX)) (* (- 308944464000) (* skoX skoX skoX skoX skoX)) (* (- 148035889) (* skoX skoX skoX skoX skoX skoX))) 9437184000000000000000000) (and (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0) (and (not (<= (+ (* (- 54263808000000000000000) skoX) (* 9555765647376384000000000 skoS) (* (- 407686348800000000000000) skoC) (* (- 156008448000000000000) (* skoX skoX)) (* (- 299016192000000000) (* skoX skoX skoX)) (* (- 376106304000000) (* skoX skoX skoX skoX)) (* (- 308944464000) (* skoX skoX skoX skoX skoX)) (* (- 148035889) (* skoX skoX skoX skoX skoX skoX))) 9437184000000000000000000)) (and (<= skoX 0) (and (or (not (<= (+ (* (- 1104000000000000) skoX) (* 388825099584000000 skoS) (* (- 16588800000000000) skoC) (* (- 1058000000000) (* skoX skoX)) (* (- 1117872161304000) (* skoX skoS)) (* 47692800000000 (* skoX skoC)) (* 1071294154583 (* skoX skoX skoS)) (* (- 45705600000) (* skoX skoX skoC))) 384000000000000000)) (<= skoX 0)) (and (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0) (and (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))))))
(set-info :status unsat)
(check-sat)
