(set-logic QF_NRA)
(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 12) skoSM1) (* 60 (* skoSM1 skoSM1)) (* (- 120) (* skoSM1 skoSM1 skoSM1))) (- 1))) (and (not (<= (+ (* (- 120) (* skoSM1 skoSM1)) (* 288 (* skoSM1 skoSP1)) (* (- 120) (* skoSP1 skoSP1)) (* 2880 (* skoSM1 skoSM1 skoSM1 skoSP1)) (* (- 7200) (* skoSM1 skoSM1 skoSP1 skoSP1)) (* 2880 (* skoSM1 skoSP1 skoSP1 skoSP1)) (* 28800 (* skoSM1 skoSM1 skoSM1 skoSP1 skoSP1 skoSP1))) 2)) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5))))))))))
(set-info :status sat)
(check-sat)
