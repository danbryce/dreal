(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (<= (+ (* 252 (* skoY skoX)) (* (- 63) (* skoX skoX)) (* (- 273) (* skoY skoY)) (* (- 126) (* skoY skoZ)) (* (- 126) (* skoX skoZ)) (* (- 63) (* skoZ skoZ)) (* 280 (* skoY skoY skoY skoX)) (* (- 259) (* skoY skoY skoX skoX)) (* (- 115) (* skoY skoY skoY skoY)) (* (- 14) (* skoY skoY skoX skoZ)) (* 126 (* skoY skoX skoX skoZ)) (* (- 140) (* skoY skoY skoY skoZ)) (* 126 (* skoY skoX skoZ skoZ)) (* (- 70) (* skoY skoY skoZ skoZ)) (* 60 (* skoY skoY skoY skoY skoY skoX)) (* (- 225) (* skoY skoY skoY skoY skoX skoX)) (* 110 (* skoY skoY skoY skoY skoX skoZ)) (* 140 (* skoY skoY skoY skoX skoX skoZ)) (* (- 30) (* skoY skoY skoY skoY skoY skoZ)) (* 140 (* skoY skoY skoY skoX skoZ skoZ)) (* (- 63) (* skoY skoY skoX skoX skoZ skoZ)) (* (- 15) (* skoY skoY skoY skoY skoZ skoZ)) (* (- 15) (* skoY skoY skoY skoY skoY skoY)) (* (- 45) (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* 30 (* skoY skoY skoY skoY skoY skoY skoX skoZ)) (* 30 (* skoY skoY skoY skoY skoY skoX skoX skoZ)) (* 30 (* skoY skoY skoY skoY skoY skoX skoZ skoZ)) (* (- 70) (* skoY skoY skoY skoY skoX skoX skoZ skoZ)) (* (- 15) (* skoY skoY skoY skoY skoY skoY skoX skoX skoZ skoZ))) 189) (and (or (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0) (<= (+ (* 3 skoZ) (* 3 (* skoY skoY skoX)) (* 3 (* skoY skoX skoX)) (* (- 3) (* skoY skoX skoZ)) (* skoX skoX skoX) (* skoX skoX skoZ) (* (- 1) (* skoY skoX skoX skoX skoZ)) (* skoY skoY skoX skoX skoX)) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))
(set-info :status sat)
(check-sat)
