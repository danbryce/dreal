(set-logic QF_NRA)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoSM1 () Real)
(assert (and (not (<= (+ (* (- 45) skoSP1) (* (- 1215) (* skoSP1 skoSP1)) (* (- 24435) (* skoSP1 skoSP1 skoSP1)) (* (- 393660) (* skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 5263380) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 59632200) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 578680200) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 4818398400) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 34295659200) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 206624260800) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 1033121304000) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 4132485216000) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 12397455648000) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 24794911296000) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1)) (* (- 24794911296000) (* skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1 skoSP1))) 1)) (and (not (<= skoX 1)) (and (not (<= skoSP1 0)) (and (not (<= skoSM1 0)) (and (not (<= skoS 0)) (not (<= (* (- 1) skoX) (- 5)))))))))
(set-info :status unsat)
(check-sat)
