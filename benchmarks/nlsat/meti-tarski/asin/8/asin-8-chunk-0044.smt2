(set-logic QF_NRA)

(declare-fun skoSM () Real)
(declare-fun skoSP () Real)
(declare-fun skoS2 () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoSP (+ (+ (/ 1. 20.) (* pi (/ 1. 2.))) (* skoS2 pi))) (+ (/ (- 1.) 5.) (* skoSM (+ (+ (/ (- 1.) 20.) (* pi (/ 1. 2.))) (* skoS2 pi)))))) (and (not (<= (* skoX (+ (+ (- 4.) (* skoSM (- 1.))) (* skoSP (- 1.)))) 0.)) (and (= skoX (+ 1. (* skoSM (* skoSM (- 1.))))) (and (= (+ (- 1.) (* skoSP skoSP)) skoX) (and (= (* skoS2 skoS2) 2.) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoSP) (and (<= 0. skoSM) (and (<= 0. skoS2) (and (not (<= skoX 0.)) (not (<= 1. skoX))))))))))))))
(set-info :status unsat)
(check-sat)
