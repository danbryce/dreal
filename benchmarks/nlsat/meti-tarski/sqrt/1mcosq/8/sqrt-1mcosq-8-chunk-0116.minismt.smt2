(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1814400) (* skoY skoY)) (* 151200 (* skoY skoY skoY skoY)) (* (- 5040) (* skoY skoY skoY skoY skoY skoY)) (* 90 (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) (- 3628800)) (and (<= (+ (* 7257600 (* skoY skoY)) (* (- 2116800) (* skoY skoY skoY skoY)) (* 161280 (* skoY skoY skoY skoY skoY skoY)) (* (- 5220) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 92 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) 0) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
