(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 62768369664000 (* skoY skoY)) (* (- 20922789888000) (* skoY skoY skoY skoY)) (* 2789705318400 (* skoY skoY skoY skoY skoY skoY)) (* (- 197707910400) (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* 8060532480 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 194725440) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 2949120 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 29844) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 212 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY))) 0) (and (not (<= (+ (* 360 (* skoY skoY)) (* (- 30) (* skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoY skoY)) 720)) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (<= (* (- 10) skoX) (- 1)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)))))))))
(set-info :status unsat)
(check-sat)
