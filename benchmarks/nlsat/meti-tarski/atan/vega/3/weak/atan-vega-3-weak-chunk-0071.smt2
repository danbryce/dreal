(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= 0. skoX) (and (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (* skoX (- 1.)) (* skoY (- 1.)))) (and (<= (* skoZ (+ (+ (/ (- 91.) 50.) skoX) (* skoY (+ (+ 1. (* skoX (+ (/ 91. 50.) (* skoX (- 1.))))) (* skoY (* skoX (- 1.))))))) (+ (+ (- 1.) (* skoX (+ (/ 91. 50.) (* skoX (- 1.))))) (* skoY (+ (+ (/ 91. 50.) (* skoX (- 1.))) (* skoY (- 1.)))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
