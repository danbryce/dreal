(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (* skoX (- 1.)) (* skoY (- 1.))) skoZ)) (+ (+ (/ 451. 100.) (* skoX (* skoX (- 1.)))) (* skoY (+ skoX (* skoY (- 1.))))))) (and (not (<= (* skoZ (+ (* skoY (- 1.)) (* skoZ (/ 1. 2.)))) (+ (+ (/ 251. 100.) (* skoX (* skoX (/ (- 1.) 2.)))) (* skoY (+ skoX (* skoY (- 1.))))))) (and (not (<= (* skoZ (+ (* skoY (- 1.)) (* skoZ (/ 1. 2.)))) (+ (/ 51. 100.) (* skoY (* skoY (/ (- 1.) 2.)))))) (and (not (<= (* skoZ (+ (* skoX (- 1.)) (* skoZ (/ 1. 2.)))) (+ (+ (/ 251. 100.) (* skoX (* skoX (- 1.)))) (* skoY (+ skoX (* skoY (/ (- 1.) 2.))))))) (and (not (<= (* skoZ (+ (* skoX (- 1.)) (* skoZ (/ 1. 2.)))) (+ (/ 51. 100.) (* skoX (* skoX (/ (- 1.) 2.)))))) (and (not (<= (* skoY (+ (* skoX (- 1.)) (* skoY (/ 1. 2.)))) (+ (/ 51. 100.) (* skoX (* skoX (/ (- 1.) 2.)))))) (and (not (<= skoZ (/ (- 3.) 2.))) (and (not (<= skoY (/ (- 3.) 2.))) (and (not (<= skoX (/ (- 3.) 2.))) (and (not (<= (/ 3. 2.) skoZ)) (and (not (<= (/ 3. 2.) skoY)) (not (<= (/ 3. 2.) skoX))))))))))))))
(set-info :status sat)
(check-sat)
