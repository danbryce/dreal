(set-logic QF_NRA)
(declare-fun skoE () Real)
(declare-fun skoX () Real)
(declare-fun skoR () Real)
(assert (and (<= skoR 0) (and (not (<= (+ (* (- 1) skoX) (* (- 3) (* skoE skoX)) (* skoR skoR) (* (- 3) (* skoE skoE skoX)) (* (- 2) (* skoE skoR skoR)) (* (- 1) (* skoE skoE skoE skoX)) (* (- 1) (* skoE skoE skoR skoR))) 0)) (and (<= (+ skoX (* 3 (* skoE skoX)) (* (- 1) (* skoR skoR)) (* 3 (* skoE skoE skoX)) (* 2 (* skoE skoR skoR)) (* skoE skoE skoE skoX) (* skoE skoE skoR skoR)) 0) (and (<= (+ (* 4 skoR) (* (- 1) (* skoX skoX))) 4) (and (<= (+ (* 4 skoX) (* (- 4) skoR) (* (- 1) (* skoX skoX))) 0) (and (<= (* 32 skoE) 1) (and (<= (* (- 32) skoE) 1) (and (<= skoX 2) (and (<= skoR 3) (and (<= (* (- 2) skoX) (- 1)) (<= (* (- 1) skoR) 0))))))))))))
(set-info :status unsat)
(check-sat)
