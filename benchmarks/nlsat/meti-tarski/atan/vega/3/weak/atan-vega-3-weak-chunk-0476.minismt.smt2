(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ (* 63 skoY) (* 63 skoX) (* 63 skoZ) (* 70 (* skoY skoY skoX)) (* 70 (* skoY skoY skoY)) (* (- 63) (* skoY skoX skoZ)) (* 70 (* skoY skoY skoZ)) (* 15 (* skoY skoY skoY skoY skoX)) (* (- 70) (* skoY skoY skoY skoX skoZ)) (* 15 (* skoY skoY skoY skoY skoZ)) (* 15 (* skoY skoY skoY skoY skoY)) (* (- 15) (* skoY skoY skoY skoY skoY skoX skoZ))) 0) (and (<= (+ (* (- 17199) skoY) (* (- 17199) skoX) (* (- 17199) skoZ) (* 9450 (* skoY skoX)) (* 19950 (* skoY skoY)) (* 9450 (* skoX skoX)) (* 9450 (* skoY skoZ)) (* 9450 (* skoX skoZ)) (* (- 19110) (* skoY skoY skoX)) (* (- 19110) (* skoY skoY skoY)) (* 17199 (* skoY skoX skoZ)) (* (- 19110) (* skoY skoY skoZ)) (* 7350 (* skoY skoY skoY skoX)) (* 9600 (* skoY skoY skoY skoY)) (* 10500 (* skoY skoY skoX skoX)) (* 1050 (* skoY skoY skoX skoZ)) (* 7350 (* skoY skoY skoY skoZ)) (* (- 9450) (* skoY skoX skoX skoZ)) (* (- 4095) (* skoY skoY skoY skoY skoX)) (* 19110 (* skoY skoY skoY skoX skoZ)) (* (- 4095) (* skoY skoY skoY skoY skoZ)) (* (- 4095) (* skoY skoY skoY skoY skoY)) (* 640 (* skoY skoY skoY skoY skoY skoX)) (* 2250 (* skoY skoY skoY skoY skoX skoX)) (* (- 5100) (* skoY skoY skoY skoY skoX skoZ)) (* 640 (* skoY skoY skoY skoY skoY skoZ)) (* (- 10500) (* skoY skoY skoY skoX skoX skoZ)) (* 640 (* skoY skoY skoY skoY skoY skoY)) (* 4095 (* skoY skoY skoY skoY skoY skoX skoZ)) (* (- 640) (* skoY skoY skoY skoY skoY skoY skoX skoZ)) (* (- 2250) (* skoY skoY skoY skoY skoY skoX skoX skoZ))) (- 9450)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))
(set-info :status unsat)
(check-sat)
