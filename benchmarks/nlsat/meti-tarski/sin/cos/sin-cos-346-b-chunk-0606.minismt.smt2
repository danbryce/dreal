(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* (- 4311014400) (* skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 1437004800 (* skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 718502400 (* skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 59875200) (* skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 1995840 (* skoX skoX skoX skoX skoX skoX)) (* (- 239500800) (* skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 19958400 (* skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 665280) (* skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 11880 (* skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 132) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) 0)) (and (= (* skoSQ3 skoSQ3) 3) (and (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= skoX 0)) (not (<= skoSQ3 0)))))))))
(set-info :status sat)
(check-sat)
