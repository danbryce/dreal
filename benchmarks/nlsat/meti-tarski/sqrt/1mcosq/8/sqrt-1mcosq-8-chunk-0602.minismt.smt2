(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (+ (* 13168189440000 (* skoX skoX)) (* (- 4389396480000) (* skoX skoX skoX skoX)) (* 585252864000 (* skoX skoX skoX skoX skoX skoX)) (* (- 41803776000) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* 1857945600 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 56246400) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 1209600 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 18180) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 180 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 1) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 0) (and (not (<= (+ (* 1814400 (* skoX skoX)) (* (- 151200) (* skoX skoX skoX skoX)) (* 5040 (* skoX skoX skoX skoX skoX skoX)) (* (- 90) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 3628800)) (and (<= (+ (* (- 5) pi) (* 10 skoY)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status unsat)
(check-sat)
