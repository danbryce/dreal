(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 571536000000000000000000000000000000000000) skoS) (* 518400000000000000000000000000000000000000 skoC) (* 16003008000000000000000000000000000000000 (* skoX skoS)) (* (- 14515200000000000000000000000000000000000) (* skoX skoC)) (* (- 224042112000000000000000000000000000000) (* skoX skoX skoS)) (* 203212800000000000000000000000000000000 (* skoX skoX skoC)) (* 2091059712000000000000000000000000000 (* skoX skoX skoX skoS)) (* (- 1896652800000000000000000000000000000) (* skoX skoX skoX skoC)) (* (- 14408708328000000000000000000000000) (* skoX skoX skoX skoX skoS)) (* 13069123200000000000000000000000000 (* skoX skoX skoX skoX skoC)) (* 76846444416000000000000000000000 (* skoX skoX skoX skoX skoX skoS)) (* (- 69701990400000000000000000000000) (* skoX skoX skoX skoX skoX skoC)) (* (- 324996421176000000000000000000) (* skoX skoX skoX skoX skoX skoX skoS)) (* 294781334400000000000000000000 (* skoX skoX skoX skoX skoX skoX skoC)) (* 1098263768112000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoS)) (* (- 996157612800000000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoC)) (* (- 2951583876801000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* 2677173584400000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* 6192987359076000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* (- 5617222094400000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* (- 9716583615102000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* 8813227768800000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* 10464013123956000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* (- 9491168366400000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* (- 6104007655641) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* 5536514880400 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC))) 0)) (and (not (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))
(set-info :status sat)
(check-sat)
