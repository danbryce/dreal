(set-logic QF_NRA)
(declare-fun skoD () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (+ (* (- 2) skoD) (* 2 skoY) (* (- 1) (* skoX skoX)) (* 2 (* skoD skoY)) (* (- 1) (* skoY skoY)) (* (- 1) (* skoD skoD))) 1)))
(set-info :status unsat)
(check-sat)
