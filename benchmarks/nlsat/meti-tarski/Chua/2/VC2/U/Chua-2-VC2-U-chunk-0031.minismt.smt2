(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 8437500000000000000) skoS) (* 42750000000000000000 skoC) (* 236250000000000000 (* skoX skoS)) (* (- 1197000000000000000) (* skoX skoC)) (* (- 3307500000000000) (* skoX skoX skoS)) (* 16758000000000000 (* skoX skoX skoC)) (* 30870000000000 (* skoX skoX skoX skoS)) (* (- 156408000000000) (* skoX skoX skoX skoC)) (* (- 189078750000) (* skoX skoX skoX skoX skoS)) (* 957999000000 (* skoX skoX skoX skoX skoC)) (* 756315000 (* skoX skoX skoX skoX skoX skoS)) (* (- 3831996000) (* skoX skoX skoX skoX skoX skoC)) (* (- 1764735) (* skoX skoX skoX skoX skoX skoX skoS)) (* 8941324 (* skoX skoX skoX skoX skoX skoX skoC))) 0) (and (<= (+ (* 8437500000000000000 skoS) (* (- 42750000000000000000) skoC) (* (- 236250000000000000) (* skoX skoS)) (* 1197000000000000000 (* skoX skoC)) (* 3307500000000000 (* skoX skoX skoS)) (* (- 16758000000000000) (* skoX skoX skoC)) (* (- 30870000000000) (* skoX skoX skoX skoS)) (* 156408000000000 (* skoX skoX skoX skoC)) (* 189078750000 (* skoX skoX skoX skoX skoS)) (* (- 957999000000) (* skoX skoX skoX skoX skoC)) (* (- 756315000) (* skoX skoX skoX skoX skoX skoS)) (* 3831996000 (* skoX skoX skoX skoX skoX skoC)) (* 1764735 (* skoX skoX skoX skoX skoX skoX skoS)) (* (- 8941324) (* skoX skoX skoX skoX skoX skoX skoC))) 0) (and (<= skoX 0) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))
(set-info :status sat)
(check-sat)
