(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 32591820000) skoX) (* 156450431 (* skoX skoX))) (- 2446800000000))) (and (not (<= (+ (* 2430156872400000000 skoS) (* (- 103680000000000000) skoC) (* (- 33657672682740000) (* skoX skoS)) (* 1435968000000000 (* skoX skoC)) (* 155386255551983 (* skoX skoX skoS)) (* (- 6629385600000) (* skoX skoX skoC))) 0)) (or (not (<= (+ (* (- 2025130727) skoS) (* 86400000 skoC)) 0)) (not (<= (+ (* 2025130727 skoS) (* (- 86400000) skoC)) 0))))))
(set-info :status sat)
(check-sat)
