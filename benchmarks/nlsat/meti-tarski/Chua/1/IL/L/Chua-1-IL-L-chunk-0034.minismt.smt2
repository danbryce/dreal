(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 42) skoS) (* (- 235) skoC)) 0)) (and (not (<= (+ (* (- 402762000) skoX) (* (- 1258807) (* skoX skoX))) 41844000000)) (and (not (<= (+ (* 114000 skoX) (* 361 (* skoX skoX))) (- 12000000))) (not (<= skoX 0))))))
(set-info :status unsat)
(check-sat)
