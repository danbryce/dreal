(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ (* 19440000000000000000000000000000000000000 skoS) (* (- 98496000000000000000000000000000000000000) skoC) (* (- 544320000000000000000000000000000000000) (* skoX skoS)) (* 2757888000000000000000000000000000000000 (* skoX skoC)) (* 7620480000000000000000000000000000000 (* skoX skoX skoS)) (* (- 38610432000000000000000000000000000000) (* skoX skoX skoC)) (* (- 71124480000000000000000000000000000) (* skoX skoX skoX skoS)) (* 360364032000000000000000000000000000 (* skoX skoX skoX skoC)) (* 490092120000000000000000000000000 (* skoX skoX skoX skoX skoS)) (* (- 2483133408000000000000000000000000) (* skoX skoX skoX skoX skoC)) (* (- 2613824640000000000000000000000) (* skoX skoX skoX skoX skoX skoS)) (* 13243378176000000000000000000000 (* skoX skoX skoX skoX skoX skoC)) (* 11054300040000000000000000000 (* skoX skoX skoX skoX skoX skoX skoS)) (* (- 56008453536000000000000000000) (* skoX skoX skoX skoX skoX skoX skoC)) (* (- 37355910480000000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoS)) (* 189269946432000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoC)) (* 100394009415000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* (- 508662981036000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* (- 210645828540000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* 1067272197936000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* 330496041330000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* (- 1674513276072000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* (- 355918813740000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* 1803321989616000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC)) (* 207619308015 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoS)) (* (- 1051937827276) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoC))) 0) (and (not (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))
(set-info :status sat)
(check-sat)
