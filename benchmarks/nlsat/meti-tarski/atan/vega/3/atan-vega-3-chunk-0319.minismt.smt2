(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoY) 1) (and (not (= skoY 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX) (* skoX skoX skoZ) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* (- 1) (* skoX skoX skoX skoY skoZ)) (* skoX skoX skoX skoY skoY)) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))))
(set-info :status sat)
(check-sat)
