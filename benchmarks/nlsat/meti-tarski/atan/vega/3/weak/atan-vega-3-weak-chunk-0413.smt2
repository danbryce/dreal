(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoX (* skoX (+ 70. (* skoX (* skoX 15.))))) (- 63.))) (and (not (<= (* skoZ (+ (+ (/ (- 5733.) 50.) (* skoX (+ 63. (* skoX (+ (/ (- 637.) 5.) (* skoX (+ 49. (* skoX (+ (/ (- 273.) 10.) (* skoX (/ 64. 15.))))))))))) (* skoY (+ (+ 63. (* skoX (+ (/ 5733. 50.) (* skoX (+ 7. (* skoX (+ (/ 637. 5.) (* skoX (+ (- 34.) (* skoX (+ (/ 273. 10.) (* skoX (/ (- 64.) 15.))))))))))))) (* skoY (* skoX (+ (- 63.) (* skoX (* skoX (+ (- 70.) (* skoX (* skoX (- 15.))))))))))))) (+ (+ (- 63.) (* skoX (+ (/ 5733. 50.) (* skoX (+ (- 133.) (* skoX (+ (/ 637. 5.) (* skoX (+ (- 64.) (* skoX (+ (/ 273. 10.) (* skoX (/ (- 64.) 15.))))))))))))) (* skoY (+ (+ (/ 5733. 50.) (* skoX (+ (- 63.) (* skoX (+ (/ 637. 5.) (* skoX (+ (- 49.) (* skoX (+ (/ 273. 10.) (* skoX (/ (- 64.) 15.))))))))))) (* skoY (+ (- 63.) (* skoX (* skoX (+ (- 70.) (* skoX (* skoX (- 15.))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
