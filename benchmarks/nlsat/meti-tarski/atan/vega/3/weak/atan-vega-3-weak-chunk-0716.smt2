(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoY (+ (* skoX 6435.) (* skoY (+ (- 12012.) (* skoY (+ (* skoX 12012.) (* skoY (+ (- 6930.) (* skoY (+ (* skoX 6930.) (* skoY (+ (- 1260.) (* skoY (+ (* skoX 1260.) (* skoY (+ (- 35.) (* skoY (* skoX 35.)))))))))))))))))) 6435.) (and (not (<= (* skoY (+ (* skoX (- 6435.)) (* skoY (+ 12012. (* skoY (+ (* skoX (- 12012.)) (* skoY (+ 6930. (* skoY (+ (* skoX (- 6930.)) (* skoY (+ 1260. (* skoY (+ (* skoX (- 1260.)) (* skoY (+ 35. (* skoY (* skoX (- 35.))))))))))))))))))) (- 6435.))) (and (not (<= 0. skoY)) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.)))))) (and (not (<= 0. skoX)) (and (or (not (<= 0. skoX)) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))))))
(set-info :status sat)
(check-sat)
