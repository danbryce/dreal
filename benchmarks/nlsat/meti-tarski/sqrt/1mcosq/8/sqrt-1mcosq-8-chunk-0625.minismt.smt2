(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (+ (* 174356582400 (* skoX skoX)) (* (- 50854003200) (* skoX skoX skoX skoX)) (* 3874590720 (* skoX skoX skoX skoX skoX skoX)) (* (- 125405280) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* 2210208 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 24388) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 184 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 1) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 0) (and (not (<= (+ (* 43589145600 (* skoX skoX)) (* (- 3632428800) (* skoX skoX skoX skoX)) (* 121080960 (* skoX skoX skoX skoX skoX skoX)) (* (- 2162160) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* 24024 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 182) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 87178291200)) (and (not (<= (+ (* (- 1) skoX) skoY) 0)) (and (<= (* (- 10) skoX) (- 1)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (<= (+ (* (- 5) pi) (* 10 skoY)) (- 2)))))))))
(set-info :status unsat)
(check-sat)
