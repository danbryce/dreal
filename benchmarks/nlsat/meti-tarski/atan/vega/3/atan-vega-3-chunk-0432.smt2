(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ (+ (+ (- 3.) (* skoX (+ (/ (- 237.) 25.) (* skoX (- 6.))))) (* skoY (+ (+ (/ (- 237.) 25.) (* skoX (+ (- 6.) (* skoX (+ (/ 237. 25.) (* skoX 6.)))))) (* skoY (+ (+ (- 6.) (* skoX (+ (/ 237. 25.) (* skoX 9.)))) (* skoY (* skoX 6.))))))) (* skoZ (+ (+ (/ (- 237.) 50.) (* skoX (- 3.))) (* skoY (+ (+ (- 3.) (* skoX (+ (/ 237. 25.) (* skoX 6.)))) (* skoY (+ (* skoX (+ 6. (* skoX (+ (/ (- 237.) 50.) (* skoX (- 3.)))))) (* skoY (* skoX (* skoX (- 3.)))))))))))) (+ (+ (/ 79. 50.) (* skoX (+ 4. (* skoX (+ (/ 237. 50.) (* skoX 3.)))))) (* skoY (+ (+ 4. (* skoX (+ (/ 158. 25.) (* skoX 4.)))) (* skoY (+ (+ (/ 237. 50.) (* skoX (+ 4. (* skoX (+ (/ 79. 50.) skoX))))) (* skoY (+ 3. (* skoX skoX)))))))))) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
