(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (+ (* (- 12012) (* skoY skoY)) (* (- 6930) (* skoY skoY skoY skoY)) (* (- 1260) (* skoY skoY skoY skoY skoY skoY)) (* (- 35) (* skoY skoY skoY skoY skoY skoY skoY skoY))) 6435) (and (not (<= (* (- 1) skoY) 0)) (and (or (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1) (and (not (<= (* (- 1) skoX) 0)) (and (or (not (<= (* (- 1) skoX) 0)) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0))))))))))))))
(set-info :status sat)
(check-sat)
