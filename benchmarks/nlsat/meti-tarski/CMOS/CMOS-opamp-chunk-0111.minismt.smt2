(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* (- 120000000000000000000) (* skoX skoX)) (* (- 3600119999) (* skoX skoX skoX skoX)) (* 3600060000000000000000000 (* skoY skoY skoX skoX)) (* 3600060000 (* skoY skoY skoX skoX skoX skoX)) (* (- 1050005000000000000000000) (* skoY skoY skoY skoY skoX skoX)) (* (- 1050005000) (* skoY skoY skoY skoY skoX skoX skoX skoX)) (* 75000000000000000000000 (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* 75000000 (* skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX))) (- 970000000000000000000000000000)) (and (not (<= (+ (* (- 3600000000000000000000000) (* skoX skoX)) (* (- 3600000000) (* skoX skoX skoX skoX)) (* 1800000000000000000000000 (* skoY skoY skoX skoX)) (* 1800000000 (* skoY skoY skoX skoX skoX skoX)) (* (- 150000000000000000000000) (* skoY skoY skoY skoY skoX skoX)) (* (- 150000000) (* skoY skoY skoY skoY skoX skoX skoX skoX))) 0)) (and (<= (* (- 1) skoX) (- 100)) (and (<= skoX 120) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963))))))))))
(set-info :status unsat)
(check-sat)
