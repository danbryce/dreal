(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(declare-fun skoS2 () Real)
(assert (and (<= (* (- 1) (* skoX skoX)) (- 2)) (and (not (<= (+ (* 160 skoX) (* (- 65) skoSP) (* 61 skoSM) (* 8 (* skoX skoX)) (* 126 (* skoSM skoS2)) (* (- 126) (* skoSP skoS2)) (* 40 (* skoX skoSP)) (* 40 (* skoX skoSM)) (* 65 (* skoX skoX skoSP)) (* (- 61) (* skoX skoX skoSM)) (* (- 126) (* skoX skoX skoSM skoS2)) (* 126 (* skoX skoX skoSP skoS2))) 8)) (and (= (+ skoX (* skoSM skoSM)) 1) (and (= (+ (* (- 1) skoX) (* skoSP skoSP)) 1) (and (= (* skoS2 skoS2) 2) (and (not (<= skoX 0)) (and (not (<= skoSP 0)) (and (not (<= skoSM 0)) (and (not (<= skoS2 0)) (not (<= (* (- 1) skoX) (- 1)))))))))))))
(set-info :status unsat)
(check-sat)
