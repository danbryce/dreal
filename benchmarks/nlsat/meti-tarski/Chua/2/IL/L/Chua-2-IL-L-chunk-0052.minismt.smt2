(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= skoX 0)) (and (or (not (<= (+ (* (- 1104000000000000) skoX) (* 388825099584000000 skoS) (* (- 16588800000000000) skoC) (* (- 1117872161304000) (* skoX skoS)) (* 47692800000000 (* skoX skoC)) (* (- 1058000000000) (* skoX skoX)) (* 1071294154583 (* skoX skoX skoS)) (* (- 45705600000) (* skoX skoX skoC))) 384000000000000000)) (<= skoX 0)) (and (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0) (and (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0))) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))))
(set-info :status sat)
(check-sat)
