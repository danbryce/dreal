(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* (- 6) skoC) (* 12 (* skoC skoC))) (- 1))) (and (not (<= (+ (* 12 skoC) (* (- 12) skoCM1) (* (- 144) (* skoC skoC skoCM1)) (* 144 (* skoC skoCM1 skoCM1))) 0)) (and (= (+ (* (- 1) skoX) (* skoCM1 skoCM1 skoCM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoC skoC skoC)) 0) (and (not (<= skoX 1)) (and (not (<= skoCM1 0)) (not (<= skoC 0)))))))))
(set-info :status sat)
(check-sat)
