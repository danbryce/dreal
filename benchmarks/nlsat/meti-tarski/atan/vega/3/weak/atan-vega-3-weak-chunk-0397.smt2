(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ (+ (* skoX 6.) (* skoY (+ (+ 6. (* skoX (* skoX (- 6.)))) (* skoY (* skoX (- 6.)))))) (* skoZ (+ 3. (* skoY (+ (* skoX (- 6.)) (* skoY (* skoX (* skoX 3.))))))))) (+ (+ (- 1.) (* skoX (* skoX (- 3.)))) (* skoY (+ (* skoX (- 4.)) (* skoY (+ (- 3.) (* skoX (* skoX (- 1.)))))))))) (and (not (<= (* skoZ (+ (+ (+ 9. (* skoX (+ (/ 1197. 50.) (* skoX (+ 21. (* skoX (/ 399. 50.))))))) (* skoY (+ (+ (/ 1197. 50.) (* skoX (+ 18. (* skoX (+ (/ (- 399.) 25.) (* skoX (+ (- 18.) (* skoX (/ (- 399.) 50.))))))))) (* skoY (+ (+ 18. (* skoX (+ (/ (- 1197.) 50.) (* skoX (+ (- 21.) (* skoX (+ (/ (- 399.) 50.) (* skoX (- 3.))))))))) (* skoY (* skoX (+ (- 18.) (* skoX (* skoX (- 6.))))))))))) (* skoZ (+ (+ (/ 1197. 100.) (* skoX (+ 9. (* skoX (/ 399. 100.))))) (* skoY (+ (+ 9. (* skoX (+ (/ (- 1197.) 50.) (* skoX (+ (- 15.) (* skoX (/ (- 399.) 50.))))))) (* skoY (+ (* skoX (+ (- 18.) (* skoX (+ (/ 1197. 100.) (* skoX (+ 3. (* skoX (/ 399. 100.)))))))) (* skoY (* skoX (* skoX (+ 9. (* skoX (* skoX 3.)))))))))))))) (+ (+ (/ (- 399.) 100.) (* skoX (+ (- 12.) (* skoX (+ (/ (- 133.) 10.) (* skoX (+ (- 12.) (* skoX (/ (- 399.) 100.))))))))) (* skoY (+ (+ (- 12.) (* skoX (+ (/ (- 399.) 25.) (* skoX (+ (- 16.) (* skoX (/ (- 133.) 25.))))))) (* skoY (+ (+ (/ (- 1197.) 100.) (* skoX (+ (- 12.) (* skoX (+ (/ (- 399.) 50.) (* skoX (+ (- 4.) (* skoX (/ (- 133.) 100.))))))))) (* skoY (+ (- 9.) (* skoX (* skoX (+ (- 6.) (* skoX (* skoX (- 1.))))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
