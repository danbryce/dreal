(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* (- 1) skoY) 0) (and (<= (+ (* (- 600) skoX) (* (- 600) skoY) (* (- 450) skoZ) (* (- 790) (* skoX skoX)) (* (- 948) (* skoX skoY)) (* (- 711) (* skoY skoY)) (* (- 1422) (* skoX skoZ)) (* (- 1422) (* skoY skoZ)) (* (- 711) (* skoZ skoZ)) (* (- 600) (* skoX skoX skoX)) (* (- 800) (* skoX skoX skoY)) (* (- 600) (* skoX skoY skoY)) (* (- 1050) (* skoX skoX skoZ)) (* (- 900) (* skoX skoY skoZ)) (* (- 900) (* skoY skoY skoZ)) (* (- 450) (* skoX skoZ skoZ)) (* (- 450) (* skoY skoZ skoZ)) (* (- 450) (* skoY skoY skoY)) (* (- 237) (* skoX skoX skoX skoX)) (* (- 316) (* skoX skoX skoX skoY)) (* (- 474) (* skoX skoX skoY skoY)) (* 948 (* skoX skoX skoY skoZ)) (* 1422 (* skoX skoY skoY skoZ)) (* (- 474) (* skoX skoX skoX skoZ)) (* (- 237) (* skoX skoX skoZ skoZ)) (* 1422 (* skoX skoY skoZ skoZ)) (* (- 200) (* skoX skoX skoX skoY skoY)) (* (- 300) (* skoX skoX skoY skoY skoY)) (* 900 (* skoX skoX skoX skoY skoZ)) (* 1050 (* skoX skoX skoY skoY skoZ)) (* 900 (* skoX skoY skoY skoY skoZ)) (* 750 (* skoX skoX skoY skoZ skoZ)) (* 900 (* skoX skoY skoY skoZ skoZ)) (* (- 79) (* skoX skoX skoX skoX skoY skoY)) (* 474 (* skoX skoX skoX skoY skoY skoZ)) (* 474 (* skoX skoX skoX skoX skoY skoZ)) (* 474 (* skoX skoX skoX skoY skoZ skoZ)) (* (- 711) (* skoX skoX skoY skoY skoZ skoZ)) (* (- 50) (* skoX skoX skoX skoX skoY skoY skoY)) (* 150 (* skoX skoX skoX skoX skoY skoY skoZ)) (* 300 (* skoX skoX skoX skoY skoY skoY skoZ)) (* (- 150) (* skoX skoX skoX skoY skoY skoZ skoZ)) (* (- 450) (* skoX skoX skoY skoY skoY skoZ skoZ)) (* (- 237) (* skoX skoX skoX skoX skoY skoY skoZ skoZ)) (* (- 150) (* skoX skoX skoX skoX skoY skoY skoY skoZ skoZ))) 237) (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (+ (* 3 (* skoX skoX)) (* 4 (* skoX skoY)) (* 3 (* skoY skoY)) (* 6 (* skoX skoZ)) (* 6 (* skoY skoZ)) (* 3 (* skoZ skoZ)) (* skoX skoX skoY skoY) (* (- 6) (* skoX skoX skoY skoZ)) (* (- 6) (* skoX skoY skoY skoZ)) (* (- 6) (* skoX skoY skoZ skoZ)) (* 3 (* skoX skoX skoY skoY skoZ skoZ))) (- 1))) (and (or (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoX skoY skoZ (* skoX skoY) (* (- 1) (* skoX skoY skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (or (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0) (<= (+ (* 3 skoZ) (* skoX skoX skoX) (* 3 (* skoX skoX skoY)) (* 3 (* skoX skoY skoY)) (* skoX skoX skoZ) (* (- 3) (* skoX skoY skoZ)) (* skoX skoX skoX skoY skoY) (* (- 1) (* skoX skoX skoX skoY skoZ))) 0))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))))))
(set-info :status sat)
(check-sat)
