(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* 12 skoC) (* (- 84) (* skoC skoC)) (* 384 (* skoC skoC skoC)) (* (- 1152) (* skoC skoC skoC skoC)) (* 2304 (* skoC skoC skoC skoC skoC)) (* (- 2304) (* skoC skoC skoC skoC skoC skoC))) 1)) (and (not (<= (+ (* (- 12) skoC) skoCM1 (* 84 (* skoC skoC)) (* (- 12) (* skoC skoCM1)) (* (- 384) (* skoC skoC skoC)) (* 84 (* skoC skoC skoCM1)) (* 1152 (* skoC skoC skoC skoC)) (* (- 384) (* skoC skoC skoC skoCM1)) (* (- 2304) (* skoC skoC skoC skoC skoC)) (* 1152 (* skoC skoC skoC skoC skoCM1)) (* 2304 (* skoC skoC skoC skoC skoC skoC)) (* (- 2304) (* skoC skoC skoC skoC skoC skoCM1))) (- 1))) (and (not (<= skoX 1)) (and (not (<= skoCM1 0)) (not (<= skoC 0)))))))
(set-info :status unsat)
(check-sat)
