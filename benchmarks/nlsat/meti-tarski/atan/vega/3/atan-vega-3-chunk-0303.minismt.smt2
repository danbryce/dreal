(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* 1413 skoY) (* 1413 skoX) (* 1413 skoZ) (* (- 900) (* skoY skoX)) (* (- 1200) (* skoX skoX)) (* (- 1200) (* skoY skoY)) (* (- 900) (* skoY skoZ)) (* (- 900) (* skoX skoZ)) (* 471 (* skoX skoX skoX)) (* 471 (* skoY skoX skoX)) (* 471 (* skoY skoY skoX)) (* (- 1413) (* skoY skoX skoZ)) (* 471 (* skoX skoX skoZ)) (* 471 (* skoY skoY skoZ)) (* 471 (* skoY skoY skoY)) (* (- 700) (* skoY skoY skoX skoX)) (* 600 (* skoY skoX skoX skoZ)) (* 600 (* skoY skoY skoX skoZ)) (* 157 (* skoY skoY skoX skoX skoX)) (* 157 (* skoY skoY skoY skoX skoX)) (* (- 471) (* skoY skoX skoX skoX skoZ)) (* 157 (* skoY skoY skoX skoX skoZ)) (* (- 471) (* skoY skoY skoY skoX skoZ)) (* 100 (* skoY skoY skoY skoX skoX skoX)) (* 300 (* skoY skoY skoX skoX skoX skoZ)) (* 300 (* skoY skoY skoY skoX skoX skoZ)) (* (- 157) (* skoY skoY skoY skoX skoX skoX skoZ))) 900) (and (not (<= (* (- 1) skoY) 0)) (and (not (<= (+ skoY skoX skoZ (* (- 1) (* skoY skoX skoZ))) 0)) (and (not (<= (+ (* 3 skoY) (* 3 skoX) (* 3 skoZ) (* skoY skoY skoX) (* (- 3) (* skoY skoX skoZ)) (* skoY skoY skoZ) (* skoY skoY skoY) (* (- 1) (* skoY skoY skoY skoX skoZ))) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0) (<= (+ (* 3 skoZ) (* skoX skoX skoX) (* 3 (* skoY skoX skoX)) (* 3 (* skoY skoY skoX)) (* (- 3) (* skoY skoX skoZ)) (* skoX skoX skoZ) (* skoY skoY skoX skoX skoX) (* (- 1) (* skoY skoX skoX skoX skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))))
(set-info :status sat)
(check-sat)
