(set-logic QF_NRA)
(set-info :source | KeYmaera example: ternary1, node 46
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (not (>= (- (+ (+ (* x x x x x x) (* y y y y y y)) (* z z z z z z)) (* (* (* 3. (* x x)) (* y y)) (* z z))) 0. )))
(check-sat)
