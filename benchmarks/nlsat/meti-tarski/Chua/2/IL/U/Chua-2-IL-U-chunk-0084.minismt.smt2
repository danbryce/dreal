(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (+ (* (- 602288632627200000000000000000000000000000000000000000000) skoX) (* 8341697561886720000000000000000000000000000000000000000 (* skoX skoX)) (* (- 77021674154754048000000000000000000000000000000000000) (* skoX skoX skoX)) (* 525041107685395660800000000000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 2770216891978182819840000000000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 11590183486073303433216000000000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 38747182378441612684492800000000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 103017341363754028724328960000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 213834186866934396057502464000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 331903839184409810432356195200000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 353605244054159682652933331040000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 204059692922921316864296943121 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 21743271936000000000000000000000000000000000000000000000000)) (and (not (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0))))))
(set-info :status unsat)
(check-sat)
