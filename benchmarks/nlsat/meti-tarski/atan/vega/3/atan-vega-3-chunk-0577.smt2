(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoX) (and (<= (* skoZ (+ (- 63.) (* skoY (+ (* skoX 63.) (* skoY (+ (- 70.) (* skoY (+ (* skoX 70.) (* skoY (+ (- 15.) (* skoY (* skoX 15.)))))))))))) (+ (* skoX 63.) (* skoY (+ 63. (* skoY (+ (* skoX 70.) (* skoY (+ 70. (* skoY (+ (* skoX 15.) (* skoY 15.))))))))))) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
