(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoY) (and (<= (* skoZ (+ (- 63.) (* skoY (+ (* skoX 63.) (* skoY (+ (- 70.) (* skoY (+ (* skoX 70.) (* skoY (+ (- 15.) (* skoY (* skoX 15.)))))))))))) (+ (* skoX 63.) (* skoY (+ 63. (* skoY (+ (* skoX 70.) (* skoY (+ 70. (* skoY (+ (* skoX 15.) (* skoY 15.))))))))))) (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (* skoX (- 1.)) (* skoY (- 1.))))) (and (or (not (<= 0. skoX)) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))))
(set-info :status sat)
(check-sat)
