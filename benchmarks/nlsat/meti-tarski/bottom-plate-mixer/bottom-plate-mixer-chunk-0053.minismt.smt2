(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSB () Real)
(declare-fun skoS () Real)
(declare-fun skoCB () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 260) skoSB) (* (- 52000) skoS) (* (- 196) skoCB) (* (- 11400) skoC)) (- 63475))) (not (<= (* 366500000 skoX) 177))))
(set-info :status sat)
(check-sat)
