(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (+ (* 70 (* skoX skoX)) (* 15 (* skoX skoX skoX skoX))) (- 63))) (and (not (<= (+ (* (- 17199) skoX) (* (- 17199) skoY) (* (- 17199) skoZ) (* 19950 (* skoX skoX)) (* 9450 (* skoX skoY)) (* 9450 (* skoX skoZ)) (* 9450 (* skoY skoZ)) (* 9450 (* skoY skoY)) (* (- 19110) (* skoX skoX skoX)) (* (- 19110) (* skoX skoX skoY)) (* (- 19110) (* skoX skoX skoZ)) (* 17199 (* skoX skoY skoZ)) (* 9600 (* skoX skoX skoX skoX)) (* 7350 (* skoX skoX skoX skoY)) (* 7350 (* skoX skoX skoX skoZ)) (* 1050 (* skoX skoX skoY skoZ)) (* (- 9450) (* skoX skoY skoY skoZ)) (* 10500 (* skoX skoX skoY skoY)) (* (- 4095) (* skoX skoX skoX skoX skoX)) (* (- 4095) (* skoX skoX skoX skoX skoY)) (* (- 4095) (* skoX skoX skoX skoX skoZ)) (* 19110 (* skoX skoX skoX skoY skoZ)) (* 640 (* skoX skoX skoX skoX skoX skoX)) (* 640 (* skoX skoX skoX skoX skoX skoY)) (* 640 (* skoX skoX skoX skoX skoX skoZ)) (* (- 5100) (* skoX skoX skoX skoX skoY skoZ)) (* (- 10500) (* skoX skoX skoX skoY skoY skoZ)) (* 2250 (* skoX skoX skoX skoX skoY skoY)) (* 4095 (* skoX skoX skoX skoX skoX skoY skoZ)) (* (- 640) (* skoX skoX skoX skoX skoX skoX skoY skoZ)) (* (- 2250) (* skoX skoX skoX skoX skoX skoY skoY skoZ))) (- 9450))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))
(set-info :status sat)
(check-sat)
