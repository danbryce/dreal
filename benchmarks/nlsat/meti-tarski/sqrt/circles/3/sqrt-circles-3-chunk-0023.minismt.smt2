(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoA () Real)
(declare-fun skoD () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1) skoA) (* (- 1) skoD)) 0) (and (not (<= (+ (* skoY skoY) (* (- 2) (* skoY skoA)) (* (- 2) (* skoY skoD)) (* skoX skoX)) 0)) (and (not (<= (+ (* (- 2) skoA) (* (- 2) skoD) (* skoY skoY) (* (- 2) (* skoY skoA)) (* (- 2) (* skoY skoD)) (* skoX skoX) (* skoA skoA) (* 2 (* skoA skoD)) (* skoD skoD)) (- 1))) (and (<= (+ (* skoY skoY) (* (- 2) (* skoY skoA)) (* skoX skoX)) 0) (and (<= (* (- 1) skoD) 0) (<= (* (- 1) skoA) 0)))))))
(set-info :status unsat)
(check-sat)
