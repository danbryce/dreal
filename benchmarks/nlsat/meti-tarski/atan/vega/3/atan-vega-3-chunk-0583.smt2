(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoY (* skoX (- 1.))) (- 1.))) (and (not (<= (* skoZ (+ (+ (/ 9891. 100.) (* skoX (- 63.))) (* skoY (+ (+ (- 63.) (* skoX (+ (/ (- 9891.) 100.) (* skoX 63.)))) (* skoY (+ (+ (/ 1099. 10.) (* skoX (- 7.))) (* skoY (+ (+ (- 49.) (* skoX (+ (/ (- 1099.) 10.) (* skoX 70.)))) (* skoY (+ (+ (/ 471. 20.) (* skoX 34.)) (* skoY (+ (+ (/ (- 64.) 15.) (* skoX (+ (/ (- 471.) 20.) (* skoX 15.)))) (* skoY (* skoX (/ 64. 15.))))))))))))))) (+ (+ 63. (* skoX (+ (/ (- 9891.) 100.) (* skoX 63.)))) (* skoY (+ (+ (/ (- 9891.) 100.) (* skoX 63.)) (* skoY (+ (+ 133. (* skoX (+ (/ (- 1099.) 10.) (* skoX 70.)))) (* skoY (+ (+ (/ (- 1099.) 10.) (* skoX 49.)) (* skoY (+ (+ 64. (* skoX (+ (/ (- 471.) 20.) (* skoX 15.)))) (* skoY (+ (+ (/ (- 471.) 20.) (* skoX (/ 64. 15.))) (* skoY (/ 64. 15.))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
