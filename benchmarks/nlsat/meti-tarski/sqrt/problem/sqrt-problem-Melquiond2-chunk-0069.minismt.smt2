(set-logic QF_NRA)
(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* (- 746155) skoSXY) (* 2048000 skoX) (* (- 589824) (* skoSXY skoX))) 0)) (and (= (+ (* (- 1) skoX) (* (- 1) skoY) (* skoSXY skoSXY)) 0) (and (not (<= skoY 1)) (and (not (<= (* 2 skoX) 3)) (and (not (<= skoSXY 0)) (and (not (<= (* (- 1) skoX) (- 2))) (not (<= (* (- 32) skoY) (- 33))))))))))
(set-info :status sat)
(check-sat)
