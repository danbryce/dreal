(set-logic QF_NRA)
(declare-fun skoE () Real)
(declare-fun skoR () Real)
(declare-fun skoX () Real)
(declare-fun skoEA () Real)
(assert (and (<= skoR 0) (and (not (<= (+ skoX (* 3 (* skoE skoX)) (* (- 1) (* skoR skoR)) (* 4 (* skoR skoEA)) (* 3 (* skoE skoE skoX)) (* 3 (* skoE skoR skoEA)) (* 2 (* skoE skoR skoR)) (* skoE skoE skoE skoX) (* skoE skoE skoR skoEA) (* skoE skoE skoR skoR)) 0)) (and (<= (+ (* 4 skoR) (* (- 1) (* skoX skoX))) 4) (and (<= (+ (* (- 4) skoR) (* 4 skoX) (* (- 1) (* skoX skoX))) 0) (and (<= (* 85070591730234615865843651857942052864 skoEA) 1) (and (<= (* 32 skoE) 1) (and (<= (* (- 32) skoE) 1) (and (<= (* (- 85070591730234615865843651857942052864) skoEA) 1) (and (<= skoX 2) (and (<= skoR 3) (and (<= (* (- 2) skoX) (- 1)) (<= (* (- 1) skoR) 0)))))))))))))
(set-info :status unsat)
(check-sat)
