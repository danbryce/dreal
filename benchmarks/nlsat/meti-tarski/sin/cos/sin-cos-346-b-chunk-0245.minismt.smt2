(set-logic QF_NRA)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (= (* skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3) 0)) (and (not (= (* skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3) 0)) (and (not (= (* skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3) 0)) (and (not (= (* skoSQ3 skoSQ3 skoSQ3 skoSQ3) 0)) (and (not (= (* skoSQ3 skoSQ3) 0)) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (+ (* 5000000 pi) (* (- 10000000) skoX)) 1))))))))))))
(set-info :status sat)
(check-sat)
