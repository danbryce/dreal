(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (/ (- 135.) 2.) (* skoX (+ (- 21.) (* skoX (/ (- 27.) 8.))))) (* skoY (+ (+ (- 21.) (* skoX (/ (- 27.) 4.))) (* skoY (/ (- 27.) 8.))))) (* skoZ (+ (+ (+ (/ (- 21.) 2.) (* skoX (/ (- 27.) 8.))) (* skoY (/ (- 27.) 8.))) (* skoZ (/ (- 9.) 8.)))))) (+ (+ 105. (* skoX (+ (/ 135. 2.) (* skoX (+ (/ 21. 2.) (* skoX (/ 9. 8.))))))) (* skoY (+ (+ (/ 135. 2.) (* skoX (+ 21. (* skoX (/ 27. 8.))))) (* skoY (+ (+ (/ 21. 2.) (* skoX (/ 27. 8.))) (* skoY (/ 9. 8.))))))))) (not (<= (* skoZ (+ (+ (+ (- 60.) (* skoX (+ 36. (* skoX (+ (- 9.) skoX))))) (* skoY (+ (+ (- 24.) (* skoX (+ 18. (* skoX (+ (- 6.) skoX))))) (* skoY (+ (+ 27. (* skoX (+ (- 15.) (* skoX 3.)))) (* skoY (+ (+ (- 8.) (* skoX 3.)) skoY))))))) (* skoZ (+ (+ (+ 48. (* skoX (+ (- 21.) (* skoX 3.)))) (* skoY (+ (+ 27. (* skoX (+ (- 15.) (* skoX 3.)))) (* skoY (+ (+ (- 18.) (* skoX 6.)) (* skoY 3.)))))) (* skoZ (+ (+ (+ (- 11.) (* skoX 3.)) (* skoY (+ (+ (- 8.) (* skoX 3.)) (* skoY 3.)))) (* skoZ (+ 1. skoY)))))))) (+ (+ 120. (* skoX (+ (- 60.) (* skoX (+ 12. (* skoX (- 1.))))))) (* skoY (+ (+ 60. (* skoX (+ (- 36.) (* skoX (+ 9. (* skoX (- 1.))))))) (* skoY (+ (+ (- 48.) (* skoX (+ 21. (* skoX (- 3.))))) (* skoY (+ (+ 11. (* skoX (- 3.))) (* skoY (- 1.)))))))))))))
(set-info :status sat)
(check-sat)
