(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 4784062500000000000000000000000000000000000000000000000000) skoX) (* 574087500000000000000000000000000000000000000000000000 (* skoX skoX)) (* (- 45927000000000000000000000000000000000000000000000) (* skoX skoX skoX)) (* 2712563437500000000000000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 124002900000000000000000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 4495105125000000000000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 130203045000000000000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 2999320143750000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 53941261500000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 725416965000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 6696156600000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 33480783 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 19933593750000000000000000000000000000000000000000000000000000)) (and (not (<= skoX 0)) (and (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (and (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0) (and (or (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (<= skoX 0)) (and (or (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))))
(set-info :status unsat)
(check-sat)
