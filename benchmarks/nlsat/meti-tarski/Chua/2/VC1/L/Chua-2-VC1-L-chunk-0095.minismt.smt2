(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 215250) skoX) (* 1813 (* skoX skoX))) (- 27750000))) (and (not (<= (+ (* 330750000 skoS) (* (- 300000000) skoC) (* (- 4630500) (* skoX skoS)) (* 4200000 (* skoX skoC)) (* 21609 (* skoX skoX skoS)) (* (- 19600) (* skoX skoX skoC))) 0)) (or (not (<= (+ (* (- 441) skoS) (* 400 skoC)) 0)) (not (<= (+ (* 441 skoS) (* (- 400) skoC)) 0))))))
(set-info :status sat)
(check-sat)
