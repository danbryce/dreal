(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (/ 15. 2.) (* skoX (+ (- 3.) (* skoX (+ (/ 243. 8.) (* skoX (+ (- 8.) skoX))))))) (* skoY (+ (+ (- 3.) (* skoX (+ (/ 3. 4.) (* skoX (+ 12. (* skoX (+ (- 5.) skoX))))))) (* skoY (+ (+ (/ 243. 8.) (* skoX (+ 12. (* skoX (+ (- 12.) (* skoX 3.)))))) (* skoY (+ (+ (- 8.) (* skoX (+ (- 5.) (* skoX 3.)))) (* skoY (+ 1. skoX))))))))) (* skoZ (+ (+ (+ (/ 117. 2.) (* skoX (+ (/ 243. 8.) (* skoX (+ (- 18.) (* skoX 3.)))))) (* skoY (+ (+ (/ 243. 8.) (* skoX (+ 12. (* skoX (+ (- 12.) (* skoX 3.)))))) (* skoY (+ (+ (- 18.) (* skoX (+ (- 12.) (* skoX 6.)))) (* skoY (+ 3. (* skoX 3.)))))))) (* skoZ (+ (+ (+ (/ (- 79.) 8.) (* skoX (+ (- 8.) (* skoX 3.)))) (* skoY (+ (+ (- 8.) (* skoX (+ (- 5.) (* skoX 3.)))) (* skoY (+ 3. (* skoX 3.)))))) (* skoZ (+ (+ 1. skoX) (* skoY (+ 1. skoX)))))))))) (+ (+ 15. (* skoX (+ (/ (- 15.) 2.) (* skoX (+ (/ (- 117.) 2.) (* skoX (+ (/ 79. 8.) (* skoX (- 1.))))))))) (* skoY (+ (+ (/ (- 15.) 2.) (* skoX (+ 3. (* skoX (+ (/ (- 243.) 8.) (* skoX (+ 8. (* skoX (- 1.))))))))) (* skoY (+ (+ (/ (- 117.) 2.) (* skoX (+ (/ (- 243.) 8.) (* skoX (+ 18. (* skoX (- 3.))))))) (* skoY (+ (+ (/ 79. 8.) (* skoX (+ 8. (* skoX (- 3.))))) (* skoY (+ (- 1.) (* skoX (- 1.))))))))))))) (not (<= (* skoZ (+ (+ (+ 60. (* skoX (+ (- 36.) (* skoX (+ 9. (* skoX (- 1.))))))) (* skoY (+ (+ 24. (* skoX (+ (- 18.) (* skoX (+ 6. (* skoX (- 1.))))))) (* skoY (+ (+ (- 27.) (* skoX (+ 15. (* skoX (- 3.))))) (* skoY (+ (+ 8. (* skoX (- 3.))) (* skoY (- 1.))))))))) (* skoZ (+ (+ (+ (- 48.) (* skoX (+ 21. (* skoX (- 3.))))) (* skoY (+ (+ (- 27.) (* skoX (+ 15. (* skoX (- 3.))))) (* skoY (+ (+ 18. (* skoX (- 6.))) (* skoY (- 3.))))))) (* skoZ (+ (+ (+ 11. (* skoX (- 3.))) (* skoY (+ (+ 8. (* skoX (- 3.))) (* skoY (- 3.))))) (* skoZ (+ (- 1.) (* skoY (- 1.)))))))))) (+ (+ (- 120.) (* skoX (+ 60. (* skoX (+ (- 12.) skoX))))) (* skoY (+ (+ (- 60.) (* skoX (+ 36. (* skoX (+ (- 9.) skoX))))) (* skoY (+ (+ 48. (* skoX (+ (- 21.) (* skoX 3.)))) (* skoY (+ (+ (- 11.) (* skoX 3.)) skoY)))))))))))
(set-info :status sat)
(check-sat)
