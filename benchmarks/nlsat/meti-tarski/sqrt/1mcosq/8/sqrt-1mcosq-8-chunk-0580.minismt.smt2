(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (+ (* (- 62768369664000) (* skoX skoX)) (* 20922789888000 (* skoX skoX skoX skoX)) (* (- 2789705318400) (* skoX skoX skoX skoX skoX skoX)) (* 197707910400 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 8060532480) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 194725440 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 2949120) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 29844 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 212) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) 0)) (and (not (<= (+ (* (- 1) skoX) skoY) 0)) (and (<= (* (- 10) skoX) (- 1)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (<= (+ (* (- 5) pi) (* 10 skoY)) (- 2))))))))
(set-info :status unsat)
(check-sat)
