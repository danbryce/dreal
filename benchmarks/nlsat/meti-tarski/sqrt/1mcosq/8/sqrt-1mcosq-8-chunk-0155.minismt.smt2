(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY skoY) 2)) (and (not (<= (+ (* (- 174356582400) (* skoY skoY)) (* 50854003200 (* skoY skoY skoY skoY)) (* (- 3874590720) (* skoY skoY skoY skoY skoY skoY)) (* 125405280 (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 2210208) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 24388 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 184) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) 0)) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
