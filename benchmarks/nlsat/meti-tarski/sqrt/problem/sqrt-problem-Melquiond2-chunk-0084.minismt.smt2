(set-logic QF_NRA)
(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (<= (+ (* 2880 (* skoSXY skoSXY skoSXY skoSXY skoSXY skoSXY)) (* (- 3680) (* skoSXY skoSXY skoSXY skoSXY skoSXY skoX)) (* (- 8200) (* skoSXY skoSXY skoSXY skoSXY skoX skoX)) (* (- 2820) (* skoSXY skoSXY skoSXY skoX skoX skoX)) (* (- 125) (* skoSXY skoSXY skoX skoX skoX skoX)) (* 2304 (* skoSXY skoSXY skoSXY skoSXY skoSXY skoSXY skoX)) (* 3456 (* skoSXY skoSXY skoSXY skoSXY skoSXY skoX skoX)) (* 1440 (* skoSXY skoSXY skoSXY skoSXY skoX skoX skoX)) (* 144 (* skoSXY skoSXY skoSXY skoX skoX skoX skoX))) 0) (and (not (<= (+ (* 16 (* skoSXY skoSXY skoSXY skoSXY skoSXY skoSXY)) (* 24 (* skoSXY skoSXY skoSXY skoSXY skoSXY skoX)) (* 10 (* skoSXY skoSXY skoSXY skoSXY skoX skoX)) (* skoSXY skoSXY skoSXY skoX skoX skoX)) 0)) (and (= (+ (* (- 1) skoX) (* (- 1) skoY) (* skoSXY skoSXY)) 0) (and (not (<= skoY 1)) (and (not (<= (* 2 skoX) 3)) (and (not (<= skoSXY 0)) (and (not (<= (* (- 1) skoX) (- 2))) (not (<= (* (- 32) skoY) (- 33)))))))))))
(set-info :status sat)
(check-sat)
