(set-logic QF_NRA)
(declare-fun skoEC1 () Real)
(declare-fun skoXC1 () Real)
(declare-fun skoRC1 () Real)
(assert (and (not (<= (+ (* 14 skoXC1) (* (- 8) skoRC1) (* (- 8) (* skoXC1 skoRC1))) 0)) (and (not (<= (+ (* (- 18) skoXC1) (* 8 skoRC1) (* 8 (* skoXC1 skoRC1))) 0)) (and (or (not (<= (+ (* (- 9) skoXC1) (* 8 skoRC1)) 0)) (not (<= skoXC1 1))) (and (<= (+ (* (- 1) skoXC1) (* (- 3) (* skoEC1 skoXC1)) (* skoRC1 skoRC1) (* (- 3) (* skoEC1 skoEC1 skoXC1)) (* (- 2) (* skoEC1 skoRC1 skoRC1)) (* (- 1) (* skoEC1 skoEC1 skoEC1 skoXC1)) (* (- 1) (* skoEC1 skoEC1 skoRC1 skoRC1))) 0) (and (<= (+ skoXC1 (* 3 (* skoEC1 skoXC1)) (* (- 1) (* skoRC1 skoRC1)) (* 3 (* skoEC1 skoEC1 skoXC1)) (* 2 (* skoEC1 skoRC1 skoRC1)) (* skoEC1 skoEC1 skoEC1 skoXC1) (* skoEC1 skoEC1 skoRC1 skoRC1)) 0) (and (<= (+ (* 4 skoRC1) (* (- 1) (* skoXC1 skoXC1))) 4) (and (<= (+ (* 4 skoXC1) (* (- 4) skoRC1) (* (- 1) (* skoXC1 skoXC1))) 0) (and (<= (* 32 skoEC1) 1) (and (<= (* (- 32) skoEC1) 1) (and (<= skoXC1 2) (and (<= skoRC1 3) (and (<= (* (- 2) skoXC1) (- 1)) (<= (* (- 1) skoRC1) 0))))))))))))))
(set-info :status unsat)
(check-sat)
