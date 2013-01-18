(set-logic QF_NRA)
(set-info :source | KeYmaera example: controllability-lemma-disturbed, node 688
Andre Platzer and Jan-David Quesel. European Train Control System: A case study in formal verification. In Karin Breitman and Ana Cavalcanti, editors, 11th International Conference on Formal Engineering Methods, ICFEM, Rio de Janeiro, Brasil, Proceedings, volume 5885 of LNCS, pages 246(- 265.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const z Real)
(declare-const m Real)
(declare-const v Real)
(declare-const d Real)
(declare-const b Real)
(declare-const u Real)
(declare-const l Real)
(assert (not (=> (and (and (and (and (and (and (and (>= z m ) (<= (- (* v v) (* d d)) (* (* 2. (- b u)) (- m z)) )) (>= v 0. )) (>= d 0. )) (> b u )) (>= u 0. )) (>= l 0. )) (<= z m )) (<= v d ))))
(check-sat)
