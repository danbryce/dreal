(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoVF () Real)
(assert (and (<= (+ (* 789435000 skoT) (* (- 93000000) skoVF) (* 8721945 (* skoT skoT)) (* 110187000 (* skoT skoVF)) (* (- 783711) (* skoT skoT skoVF))) (- 1035000000)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (not (<= skoVF 0)) (and (not (<= skoT 0)) (not (<= (* (- 50) skoVF) (- 151))))))))
(set-info :status unsat)
(check-sat)
