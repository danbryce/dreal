(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* (- 3367595) skoX) (* 1456810 skoSXY) (* 589824 (* skoX skoX)) (* 1179648 (* skoX skoSXY))) 0)) (and (not (<= (+ skoX (* 2 skoSXY)) 0)) (and (not (<= skoY 1)) (and (not (<= (* 2 skoX) 3)) (and (not (<= skoSXY 0)) (and (not (<= (* (- 1) skoX) (- 2))) (not (<= (* (- 32) skoY) (- 33))))))))))
(set-info :status sat)
(check-sat)
