(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoY) (and (<= (* skoZ (+ (+ (+ (- 9.) (* skoX (+ (/ (- 711.) 25.) (* skoX (+ (- 21.) (* skoX (/ (- 237.) 25.))))))) (* skoY (+ (+ (/ (- 711.) 25.) (* skoX (+ (- 18.) (* skoX (+ (/ 474. 25.) (* skoX (+ 18. (* skoX (/ 237. 25.))))))))) (* skoY (+ (+ (- 18.) (* skoX (+ (/ 711. 25.) (* skoX (+ 21. (* skoX (+ (/ 237. 25.) (* skoX 3.)))))))) (* skoY (* skoX (+ 18. (* skoX (* skoX 6.)))))))))) (* skoZ (+ (+ (/ (- 711.) 50.) (* skoX (+ (- 9.) (* skoX (/ (- 237.) 50.))))) (* skoY (+ (+ (- 9.) (* skoX (+ (/ 711. 25.) (* skoX (+ 15. (* skoX (/ 237. 25.))))))) (* skoY (+ (* skoX (+ 18. (* skoX (+ (/ (- 711.) 50.) (* skoX (+ (- 3.) (* skoX (/ (- 237.) 50.)))))))) (* skoY (* skoX (* skoX (+ (- 9.) (* skoX (* skoX (- 3.))))))))))))))) (+ (+ (/ 237. 50.) (* skoX (+ 12. (* skoX (+ (/ 79. 5.) (* skoX (+ 12. (* skoX (/ 237. 50.))))))))) (* skoY (+ (+ 12. (* skoX (+ (/ 474. 25.) (* skoX (+ 16. (* skoX (/ 158. 25.))))))) (* skoY (+ (+ (/ 711. 50.) (* skoX (+ 12. (* skoX (+ (/ 237. 25.) (* skoX (+ 4. (* skoX (/ 79. 50.))))))))) (* skoY (+ 9. (* skoX (* skoX (+ 6. (* skoX skoX)))))))))))) (and (not (<= 0. skoX)) (and (not (<= (* skoX skoX) (- 3.))) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))))
(set-info :status sat)
(check-sat)
