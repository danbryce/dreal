(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (- 3.) (* skoY (+ (* skoX 3.) (* skoY (+ (- 1.) (* skoY skoX))))))) (+ (* skoX 3.) (* skoY (+ 3. (* skoY (+ skoX skoY)))))) (and (<= (* skoZ (+ 3. (* skoY (+ (* skoX (- 3.)) (* skoY (+ 1. (* skoY (* skoX (- 1.))))))))) (+ (* skoX (- 3.)) (* skoY (+ (- 3.) (* skoY (+ (* skoX (- 1.)) (* skoY (- 1.)))))))) (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (/ (- 273.) 50.) (* skoY (+ (+ 3. (* skoX (/ 273. 50.))) (* skoY (+ (+ (/ (- 91.) 50.) (* skoX (- 3.))) (* skoY (* skoX (/ 91. 50.))))))))) (+ (+ (- 3.) (* skoX (/ 273. 50.))) (* skoY (+ (/ 273. 50.) (* skoY (+ (+ (- 4.) (* skoX (/ 91. 50.))) (* skoY (+ (/ 91. 50.) skoX))))))))) (and (not (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (* skoX (- 1.)) (* skoY (- 1.))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))))
(set-info :status unsat)
(check-sat)
