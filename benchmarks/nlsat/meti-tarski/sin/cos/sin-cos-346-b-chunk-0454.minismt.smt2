(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* 3 (* skoSQ3 skoSQ3)) 0)) (and (not (<= (+ (* 479001600 (* skoSQ3 skoSQ3)) (* (- 159667200) (* skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 239500800) (* skoX skoX skoSQ3 skoSQ3)) (* 13305600 (* skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 79833600 (* skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 221760 (* skoX skoX skoX skoX skoX skoX)) (* (- 665280) (* skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 11880 (* skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3)) (* (- 132) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3)) 0)) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)))))))))
(set-info :status sat)
(check-sat)
