(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (/ (- 17199.) 50.) (* skoX (+ 189. (* skoX (/ (- 5733.) 50.))))) (* skoY (+ (+ 189. (* skoX (+ (/ 17199. 50.) (* skoX (+ (- 126.) (* skoX (/ 5733. 50.))))))) (* skoY (+ (+ (/ (- 1911.) 5.) (* skoX (+ 21. (* skoX (+ (/ (- 637.) 5.) (* skoX (- 63.))))))) (* skoY (+ (+ 147. (* skoX (+ (/ 1911. 5.) (* skoX (+ (- 161.) (* skoX (/ 637. 5.))))))) (* skoY (+ (+ (/ (- 819.) 10.) (* skoX (+ (- 102.) (* skoX (+ (/ (- 273.) 10.) (* skoX (- 49.))))))) (* skoY (+ (+ (/ 64. 5.) (* skoX (+ (/ 819. 10.) (* skoX (+ (/ (- 611.) 15.) (* skoX (/ 273. 10.))))))) (* skoY (* skoX (+ (/ (- 64.) 5.) (* skoX (* skoX (/ (- 64.) 15.)))))))))))))))))) (+ (+ (- 189.) (* skoX (+ (/ 17199. 50.) (* skoX (+ (- 252.) (* skoX (/ 5733. 50.))))))) (* skoY (+ (+ (/ 17199. 50.) (* skoX (+ (- 189.) (* skoX (/ 5733. 50.))))) (* skoY (+ (+ (- 399.) (* skoX (+ (/ 1911. 5.) (* skoX (+ (- 343.) (* skoX (/ 637. 5.))))))) (* skoY (+ (+ (/ 1911. 5.) (* skoX (+ (- 147.) (* skoX (+ (/ 637. 5.) (* skoX 21.)))))) (* skoY (+ (+ (- 192.) (* skoX (+ (/ 819. 10.) (* skoX (+ (- 109.) (* skoX (/ 273. 10.))))))) (* skoY (+ (+ (/ 819. 10.) (* skoX (+ (/ (- 64.) 5.) (* skoX (+ (/ 273. 10.) (* skoX (/ 161. 15.))))))) (* skoY (+ (/ (- 64.) 5.) (* skoX (* skoX (/ (- 64.) 15.))))))))))))))))) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (or (not (<= 0. skoX)) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))))
(set-info :status sat)
(check-sat)
