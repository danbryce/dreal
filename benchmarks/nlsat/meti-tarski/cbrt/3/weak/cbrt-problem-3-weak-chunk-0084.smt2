(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (/ (- 1.) 2.) skoX)) (and (not (<= (* skoZ (+ (+ (+ (/ 88. 3.) (* skoX (+ (/ 761. 3.) (* skoX (+ (/ 17. 3.) (* skoX (/ (- 2.) 3.))))))) (* skoY (+ (+ (/ 761. 3.) (* skoX (+ (/ 2870. 3.) (* skoX (+ 70. (* skoX (/ (- 4.) 3.))))))) (* skoY (+ (+ (/ 17. 3.) (* skoX (+ 70. (* skoX (/ (- 8.) 3.))))) (* skoY (+ (/ (- 2.) 3.) (* skoX (/ (- 4.) 3.))))))))) (* skoZ (+ (+ (+ (/ (- 71.) 6.) (* skoX (+ (/ 17. 3.) (* skoX (/ (- 4.) 3.))))) (* skoY (+ (+ (/ 17. 3.) (* skoX (+ 70. (* skoX (/ (- 8.) 3.))))) (* skoY (+ (/ (- 4.) 3.) (* skoX (/ (- 8.) 3.))))))) (* skoZ (+ (+ (/ (- 1.) 3.) (* skoX (/ (- 2.) 3.))) (* skoY (+ (/ (- 2.) 3.) (* skoX (/ (- 4.) 3.)))))))))) (+ (+ (/ 80. 3.) (* skoX (+ (/ (- 88.) 3.) (* skoX (+ (/ 71. 6.) (* skoX (/ 1. 3.))))))) (* skoY (+ (+ (/ (- 88.) 3.) (* skoX (+ (/ (- 761.) 3.) (* skoX (+ (/ (- 17.) 3.) (* skoX (/ 2. 3.))))))) (* skoY (+ (+ (/ 71. 6.) (* skoX (+ (/ (- 17.) 3.) (* skoX (/ 4. 3.))))) (* skoY (+ (/ 1. 3.) (* skoX (/ 2. 3.))))))))))) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX))))))))))
(set-info :status unsat)
(check-sat)
