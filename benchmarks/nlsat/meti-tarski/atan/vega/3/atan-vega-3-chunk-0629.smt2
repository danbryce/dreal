(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.)))))) (and (not (<= 0. skoX)) (and (not (<= (* skoY (* skoX (- 1.))) (- 1.))) (and (not (<= (* skoZ (+ (+ (/ 29673. 100.) (* skoX (+ (- 189.) (* skoX (/ 9891. 100.))))) (* skoY (+ (+ (- 189.) (* skoX (+ (/ (- 29673.) 100.) (* skoX (+ 126. (* skoX (/ (- 9891.) 100.))))))) (* skoY (+ (+ (/ 3297. 10.) (* skoX (+ (- 21.) (* skoX (+ (/ 1099. 10.) (* skoX 63.)))))) (* skoY (+ (+ (- 147.) (* skoX (+ (/ (- 3297.) 10.) (* skoX (+ 161. (* skoX (/ (- 1099.) 10.))))))) (* skoY (+ (+ (/ 1413. 20.) (* skoX (+ 102. (* skoX (+ (/ 471. 20.) (* skoX 49.)))))) (* skoY (+ (+ (/ (- 64.) 5.) (* skoX (+ (/ (- 1413.) 20.) (* skoX (+ (/ 611. 15.) (* skoX (/ (- 471.) 20.))))))) (* skoY (* skoX (+ (/ 64. 5.) (* skoX (* skoX (/ 64. 15.)))))))))))))))))) (+ (+ 189. (* skoX (+ (/ (- 29673.) 100.) (* skoX (+ 252. (* skoX (/ (- 9891.) 100.))))))) (* skoY (+ (+ (/ (- 29673.) 100.) (* skoX (+ 189. (* skoX (/ (- 9891.) 100.))))) (* skoY (+ (+ 399. (* skoX (+ (/ (- 3297.) 10.) (* skoX (+ 343. (* skoX (/ (- 1099.) 10.))))))) (* skoY (+ (+ (/ (- 3297.) 10.) (* skoX (+ 147. (* skoX (+ (/ (- 1099.) 10.) (* skoX (- 21.))))))) (* skoY (+ (+ 192. (* skoX (+ (/ (- 1413.) 20.) (* skoX (+ 109. (* skoX (/ (- 471.) 20.))))))) (* skoY (+ (+ (/ (- 1413.) 20.) (* skoX (+ (/ 64. 5.) (* skoX (+ (/ (- 471.) 20.) (* skoX (/ (- 161.) 15.))))))) (* skoY (+ (/ 64. 5.) (* skoX (* skoX (/ 64. 15.)))))))))))))))))) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))))
(set-info :status sat)
(check-sat)
