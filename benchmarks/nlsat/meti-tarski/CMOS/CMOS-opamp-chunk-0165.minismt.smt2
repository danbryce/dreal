(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 226800000000000000000000000 (* skoX skoX)) (* 226800000000 (* skoX skoX skoX skoX)) (* (- 113400000000000000000000000) (* skoY skoY skoX skoX)) (* (- 113400000000) (* skoY skoY skoX skoX skoX skoX)) (* 9450000000000000000000000 (* skoY skoY skoY skoY skoX skoX)) (* 9450000000 (* skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 315000000000000000000000) (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 315000000) (* skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* 5625000000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 5625000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 62500000000000000000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 62500) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX))) 0) (and (not (<= (+ (* (- 226800000000000000000000000) (* skoX skoX)) (* (- 226800000000) (* skoX skoX skoX skoX)) (* 113400000000000000000000000 (* skoY skoY skoX skoX)) (* 113400000000 (* skoY skoY skoX skoX skoX skoX)) (* (- 9450000000000000000000000) (* skoY skoY skoY skoY skoX skoX)) (* (- 9450000000) (* skoY skoY skoY skoY skoX skoX skoX skoX)) (* 315000000000000000000000 (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* 315000000 (* skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 5625000000000000000000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 5625000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* 62500000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 62500 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX))) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= skoX 120) (<= (* (- 1) skoX) (- 100))))))))))
(set-info :status unsat)
(check-sat)
