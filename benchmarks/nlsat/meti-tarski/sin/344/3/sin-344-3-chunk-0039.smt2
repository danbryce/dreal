(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (- 1.) (* skoX (* skoX (+ (/ 1. 2.) (* skoX (* skoX (/ (- 1.) 24.))))))) (* skoY (+ (* skoX (+ 1. (* skoX (* skoX (/ (- 1.) 6.))))) (* skoY (+ (+ (/ 1. 2.) (* skoX (* skoX (/ (- 1.) 4.)))) (* skoY (+ (* skoX (/ (- 1.) 6.)) (* skoY (/ (- 1.) 24.))))))))) (* skoZ (+ (+ (* skoX (+ (/ 1. 2.) (* skoX (* skoX (/ (- 1.) 12.))))) (* skoY (+ (+ (/ 1. 2.) (* skoX (* skoX (/ (- 1.) 4.)))) (* skoY (+ (* skoX (/ (- 1.) 4.)) (* skoY (/ (- 1.) 12.))))))) (* skoZ (+ (+ (+ (/ 1. 6.) (* skoX (* skoX (/ (- 1.) 12.)))) (* skoY (+ (* skoX (/ (- 1.) 6.)) (* skoY (/ (- 1.) 12.))))) (* skoZ (+ (+ (* skoX (/ (- 1.) 24.)) (* skoY (/ (- 1.) 24.))) (* skoZ (/ (- 1.) 120.)))))))))) (+ (* skoX (+ 1. (* skoX (* skoX (+ (/ (- 1.) 6.) (* skoX (* skoX (/ 1. 120.)))))))) (* skoY (+ (+ 1. (* skoX (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 24.))))))) (* skoY (+ (* skoX (+ (/ (- 1.) 2.) (* skoX (* skoX (/ 1. 12.))))) (* skoY (+ (+ (/ (- 1.) 6.) (* skoX (* skoX (/ 1. 12.)))) (* skoY (+ (* skoX (/ 1. 24.)) (* skoY (/ 1. 120.))))))))))))) (and (not (<= 3. skoX)) (and (not (<= 3. skoY)) (and (not (<= 3. skoZ)) (and (not (<= skoX (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (not (<= skoZ (/ 1. 10.))))))))))
(set-info :status unsat)
(check-sat)
