(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoX) (and (<= (* skoZ (+ (+ (+ 189. (* skoX (* skoX (+ 84. (* skoX (* skoX (+ (- 53.) (* skoX (* skoX (/ (- 128.) 15.)))))))))) (* skoY (+ (* skoX (+ (- 630.) (* skoX (* skoX (+ (- 532.) (* skoX (* skoX (+ (/ (- 458.) 15.) (* skoX (* skoX (/ 128. 15.))))))))))) (* skoY (+ (+ (- 126.) (* skoX (* skoX (+ 301. (* skoX (* skoX (+ 418. (* skoX (* skoX (/ 1253. 15.)))))))))) (* skoY (* skoX (+ 126. (* skoX (* skoX (+ 140. (* skoX (* skoX 30.))))))))))))) (* skoZ (+ (* skoX (+ (- 63.) (* skoX (* skoX (+ (- 49.) (* skoX (* skoX (/ (- 64.) 15.)))))))) (* skoY (+ (+ (- 63.) (* skoX (* skoX (+ 56. (* skoX (* skoX (+ 83. (* skoX (* skoX (/ 128. 15.)))))))))) (* skoY (+ (* skoX (+ 126. (* skoX (* skoX (+ 77. (* skoX (* skoX (+ (- 19.) (* skoX (* skoX (/ (- 64.) 15.))))))))))) (* skoY (* skoX (* skoX (+ (- 63.) (* skoX (* skoX (+ (- 70.) (* skoX (* skoX (- 15.)))))))))))))))))) (+ (* skoX (* skoX (* skoX (* skoX (* skoX (+ (/ 84. 5.) (* skoX (* skoX (/ 64. 15.))))))))) (* skoY (+ (* skoX (* skoX (* skoX (* skoX (+ 84. (* skoX (* skoX (/ 644. 15.)))))))) (* skoY (+ (* skoX (* skoX (* skoX (+ 168. (* skoX (* skoX (+ (/ 2044. 15.) (* skoX (* skoX (/ 64. 5.)))))))))) (* skoY (+ 63. (* skoX (* skoX (+ 259. (* skoX (* skoX (+ 225. (* skoX (* skoX 45.)))))))))))))))) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
