(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoX) (and (not (<= (* skoX (* skoX (+ 70. (* skoX (* skoX 15.))))) (- 63.))) (and (not (<= (* skoZ (+ (+ (+ (- 189.) (* skoX (+ (/ (- 63.) 2.) (* skoX (+ (- 84.) (* skoX (+ (- 35.) (* skoX (+ 53. (* skoX (+ (/ (- 15.) 2.) (* skoX (/ 128. 15.))))))))))))) (* skoY (+ (+ (/ (- 63.) 2.) (* skoX (+ 630. (* skoX (+ (/ (- 7.) 2.) (* skoX (+ 532. (* skoX (+ (/ 55. 2.) (* skoX (+ (/ 458. 15.) (* skoX (+ (/ 15. 2.) (* skoX (/ (- 128.) 15.))))))))))))))) (* skoY (+ (+ 126. (* skoX (+ (/ 63. 2.) (* skoX (+ (- 301.) (* skoX (+ 35. (* skoX (+ (- 418.) (* skoX (+ (/ 15. 2.) (* skoX (/ (- 1253.) 15.))))))))))))) (* skoY (* skoX (+ (- 126.) (* skoX (* skoX (+ (- 140.) (* skoX (* skoX (- 30.)))))))))))))) (* skoZ (+ (+ (/ (- 63.) 4.) (* skoX (+ 63. (* skoX (+ (/ (- 35.) 2.) (* skoX (+ 49. (* skoX (+ (/ (- 15.) 4.) (* skoX (/ 64. 15.))))))))))) (* skoY (+ (+ 63. (* skoX (+ (/ 63. 2.) (* skoX (+ (- 56.) (* skoX (+ 35. (* skoX (+ (- 83.) (* skoX (+ (/ 15. 2.) (* skoX (/ (- 128.) 15.))))))))))))) (* skoY (+ (* skoX (+ (- 126.) (* skoX (+ (/ (- 63.) 4.) (* skoX (+ (- 77.) (* skoX (+ (/ (- 35.) 2.) (* skoX (+ 19. (* skoX (+ (/ (- 15.) 4.) (* skoX (/ 64. 15.)))))))))))))) (* skoY (* skoX (* skoX (+ 63. (* skoX (* skoX (+ 70. (* skoX (* skoX 15.))))))))))))))))) (+ (+ (/ 189. 4.) (* skoX (* skoX (+ (/ 273. 4.) (* skoX (* skoX (+ (/ 115. 4.) (* skoX (+ (/ (- 84.) 5.) (* skoX (+ (/ 15. 4.) (* skoX (/ (- 64.) 15.))))))))))))) (* skoY (+ (* skoX (+ (- 63.) (* skoX (* skoX (+ (- 70.) (* skoX (+ (- 84.) (* skoX (+ (- 15.) (* skoX (/ (- 644.) 15.))))))))))) (* skoY (+ (+ (/ 63. 4.) (* skoX (* skoX (+ (/ 259. 4.) (* skoX (+ (- 168.) (* skoX (+ (/ 225. 4.) (* skoX (+ (/ (- 2044.) 15.) (* skoX (+ (/ 45. 4.) (* skoX (/ (- 64.) 5.)))))))))))))) (* skoY (+ (- 63.) (* skoX (* skoX (+ (- 259.) (* skoX (* skoX (+ (- 225.) (* skoX (* skoX (- 45.)))))))))))))))))) (and (or (not (<= 0. skoX)) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))))
(set-info :status unsat)
(check-sat)
