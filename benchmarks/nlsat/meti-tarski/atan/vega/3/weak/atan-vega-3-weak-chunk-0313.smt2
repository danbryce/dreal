(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (or (not (<= 0. skoX)) (not (<= (* skoZ (+ (+ (+ (- 3.) (* skoX (+ (/ (- 1.) 2.) (* skoX 2.)))) (* skoY (+ (+ (/ (- 1.) 2.) (* skoX (+ 10. (* skoX (+ (/ 1. 2.) (* skoX (- 2.))))))) (* skoY (+ (+ 2. (* skoX (+ (/ 1. 2.) (* skoX (- 7.))))) (* skoY (* skoX (- 2.)))))))) (* skoZ (+ (+ (/ (- 1.) 4.) skoX) (* skoY (+ (+ 1. (* skoX (+ (/ 1. 2.) (* skoX (- 2.))))) (* skoY (+ (* skoX (+ (- 2.) (* skoX (+ (/ (- 1.) 4.) skoX)))) (* skoY (* skoX skoX)))))))))) (+ (+ (/ 3. 4.) (* skoX (* skoX (+ (/ 1. 4.) (* skoX (- 1.)))))) (* skoY (+ (* skoX (- 1.)) (* skoY (+ (+ (/ 1. 4.) (* skoX (* skoX (+ (/ 3. 4.) (* skoX (- 3.)))))) (* skoY (+ (- 1.) (* skoX (* skoX (- 3.))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status sat)
(check-sat)
