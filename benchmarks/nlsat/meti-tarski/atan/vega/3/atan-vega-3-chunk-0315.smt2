(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (* skoX (- 2.)) (* skoY (+ (+ (- 2.) (* skoX (* skoX 2.))) (* skoY (* skoX 2.))))) (* skoZ (+ (- 1.) (* skoY (+ (* skoX 2.) (* skoY (* skoX (* skoX (- 1.)))))))))) (+ (+ 3. (* skoX skoX)) (* skoY (+ (* skoX (- 4.)) (* skoY (+ 1. (* skoX (* skoX 3.))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))
(set-info :status unsat)
(check-sat)
