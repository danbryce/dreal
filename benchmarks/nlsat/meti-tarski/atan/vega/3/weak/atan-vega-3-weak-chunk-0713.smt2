(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (- 6435.) (* skoY (+ (* skoX 6435.) (* skoY (+ (- 12012.) (* skoY (+ (* skoX 12012.) (* skoY (+ (- 6930.) (* skoY (+ (* skoX 6930.) (* skoY (+ (- 1260.) (* skoY (+ (* skoX 1260.) (* skoY (+ (- 35.) (* skoY (* skoX 35.)))))))))))))))))))) (+ (+ (/ 6435. 4.) (* skoX 6435.)) (* skoY (+ (* skoX (/ (- 6435.) 4.)) (* skoY (+ (+ 3003. (* skoX 18447.)) (* skoY (+ (+ 2145. (* skoX (- 3003.))) (* skoY (+ (+ (/ 3465. 2.) (* skoX 16797.)) (* skoY (+ (+ 2717. (* skoX (/ (- 3465.) 2.))) (* skoY (+ (+ 315. (* skoX 5473.)) (* skoY (+ (+ (/ 28941. 35.) (* skoX (- 315.))) (* skoY (+ (+ (/ 35. 4.) (* skoX (/ 16384. 35.))) (* skoY (+ 35. (* skoX (/ (- 35.) 4.))))))))))))))))))))))) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
