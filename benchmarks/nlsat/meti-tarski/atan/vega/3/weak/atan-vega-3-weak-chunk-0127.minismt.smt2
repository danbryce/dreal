(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (* (- 1) (* skoX skoX)) 3)) (and (not (<= (+ skoX skoY skoZ (* (- 1) (* skoX skoY skoZ))) 0)) (and (not (<= (+ (* 273 skoX) (* 273 skoY) (* 273 skoZ) (* (- 200) (* skoX skoX)) (* (- 150) (* skoX skoY)) (* (- 150) (* skoX skoZ)) (* (- 150) (* skoY skoZ)) (* (- 150) (* skoY skoY)) (* (- 273) (* skoX skoY skoZ)) (* 91 (* skoX skoX skoX)) (* 91 (* skoX skoX skoY)) (* 91 (* skoX skoX skoZ)) (* 100 (* skoX skoX skoY skoZ)) (* 150 (* skoX skoY skoY skoZ)) (* (- 50) (* skoX skoX skoY skoY)) (* (- 91) (* skoX skoX skoX skoY skoZ)) (* 50 (* skoX skoX skoX skoY skoY skoZ))) 150)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0))))))))))
(set-info :status unsat)
(check-sat)
