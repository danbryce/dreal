(set-logic QF_NRA)
(declare-fun skoSM () Real)
(declare-fun skoSP () Real)
(declare-fun skoS2 () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ skoSM skoSP (* 10 (* skoSP pi)) (* (- 10) (* skoSM pi)) (* 20 (* skoSP skoS2 pi)) (* (- 20) (* skoSM skoS2 pi))) (- 4)) (and (= (+ skoX (* skoSM skoSM)) 1) (and (= (+ (* (- 1) skoX) (* skoSP skoSP)) 1) (and (= (* skoS2 skoS2) 2) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 1) skoSP) 0) (and (<= (* (- 1) skoSM) 0) (and (<= (* (- 1) skoS2) 0) (and (not (<= skoX 0)) (not (<= (* (- 1) skoX) (- 1))))))))))))))
(set-info :status unsat)
(check-sat)
