(set-logic QF_NRA)
(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 12) skoSM1) (* 60 (* skoSM1 skoSM1)) (* (- 120) (* skoSM1 skoSM1 skoSM1))) (- 1)) (and (not (<= (+ (* 24 skoSM1) (* 12 skoSP1) (* (- 24) (* skoSP1 skoSP1)) (* (- 120) (* skoSM1 skoSM1)) (* (- 144) (* skoSM1 skoSP1)) (* 240 (* skoSM1 skoSM1 skoSM1)) (* 720 (* skoSM1 skoSM1 skoSP1)) (* 288 (* skoSM1 skoSP1 skoSP1)) (* (- 1440) (* skoSM1 skoSM1 skoSM1 skoSP1)) (* (- 1440) (* skoSM1 skoSM1 skoSP1 skoSP1)) (* 2880 (* skoSM1 skoSM1 skoSM1 skoSP1 skoSP1))) 2)) (and (= (+ (* (- 1) skoX) (* skoSP1 skoSP1)) 1) (and (= (+ (* (- 1) skoX) (* skoSM1 skoSM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoS skoS)) 0) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5)))))))))))))
(set-info :status sat)
(check-sat)
