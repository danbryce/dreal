(set-logic QF_NRA)
(declare-fun skoEC1 () Real)
(declare-fun skoXC1 () Real)
(declare-fun skoRC1 () Real)
(assert (and (<= skoRC1 0) (and (not (<= (+ (* (- 1) skoXC1) (* (- 3) (* skoEC1 skoXC1)) (* skoRC1 skoRC1) (* (- 3) (* skoEC1 skoEC1 skoXC1)) (* (- 2) (* skoEC1 skoRC1 skoRC1)) (* (- 1) (* skoEC1 skoEC1 skoEC1 skoXC1)) (* (- 1) (* skoEC1 skoEC1 skoRC1 skoRC1))) 0)) (and (<= (+ skoXC1 (* 3 (* skoEC1 skoXC1)) (* (- 1) (* skoRC1 skoRC1)) (* 3 (* skoEC1 skoEC1 skoXC1)) (* 2 (* skoEC1 skoRC1 skoRC1)) (* skoEC1 skoEC1 skoEC1 skoXC1) (* skoEC1 skoEC1 skoRC1 skoRC1)) 0) (and (<= (+ (* 4 skoRC1) (* (- 1) (* skoXC1 skoXC1))) 4) (and (<= (+ (* 4 skoXC1) (* (- 4) skoRC1) (* (- 1) (* skoXC1 skoXC1))) 0) (and (<= (* 32 skoEC1) 1) (and (<= (* (- 32) skoEC1) 1) (and (<= skoXC1 2) (and (<= skoRC1 3) (and (<= (* (- 2) skoXC1) (- 1)) (<= (* (- 1) skoRC1) 0))))))))))))
(set-info :status unsat)
(check-sat)
