(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (+ 9. (* skoX (* skoX 3.))) (* skoY (+ (* skoX (+ (- 9.) (* skoX (* skoX (- 3.))))) (* skoY (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (+ (* skoX (* skoX (* skoX (- 3.)))) (* skoY (+ (* skoX (* skoX (- 9.))) (* skoY (+ (* skoX (+ (- 9.) (* skoX (* skoX (- 4.))))) (* skoY (+ (- 3.) (* skoX (* skoX (- 4.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
