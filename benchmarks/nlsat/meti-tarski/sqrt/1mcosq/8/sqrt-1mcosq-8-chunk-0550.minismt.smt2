(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* (- 174356582400) (* skoX skoX)) (* 50854003200 (* skoX skoX skoX skoX)) (* (- 3874590720) (* skoX skoX skoX skoX skoX skoX)) (* 125405280 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 2210208) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 24388 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 184) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))
(set-info :status sat)
(check-sat)
