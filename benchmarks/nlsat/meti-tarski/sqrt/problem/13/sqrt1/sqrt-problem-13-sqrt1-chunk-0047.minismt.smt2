(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSS () Real)
(declare-fun skoSM () Real)
(assert (and (<= (+ (* 500 skoX) (* (- 957) skoSS)) 1914) (and (not (<= (+ (* (- 500) skoX) (* 957 skoSS)) (- 1914))) (and (not (<= (* (- 1) skoX) (- 1))) (and (not (<= skoX 0)) (and (<= (* (- 1) skoSM) 0) (and (<= (* (- 1) skoSS) 0) (and (= (+ skoX (* skoSM skoSM)) 1) (= (+ (* skoX skoX) (* skoSS skoSS)) 1)))))))))
(set-info :status sat)
(check-sat)
