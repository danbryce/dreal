(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 42) skoS) (* (- 235) skoC)) 0)) (and (not (<= (+ (* (- 15365376000000000000000) skoX) (* (- 145971072000000000000) (* skoX skoX)) (* (- 924483456000000000) (* skoX skoX skoX)) (* (- 3842384364000000) (* skoX skoX skoX skoX)) (* (- 10429328988000) (* skoX skoX skoX skoX skoX)) (* (- 16513104231) (* skoX skoX skoX skoX skoX skoX))) 803404800000000000000000)) (and (not (<= (+ (* 43776000000000000000 skoX) (* 415872000000000000 (* skoX skoX)) (* 2633856000000000 (* skoX skoX skoX)) (* 10946964000000 (* skoX skoX skoX skoX)) (* 29713188000 (* skoX skoX skoX skoX skoX)) (* 47045881 (* skoX skoX skoX skoX skoX skoX))) (- 2304000000000000000000))) (and (or (not (<= (+ (* 42 skoS) (* 235 skoC)) 0)) (<= skoX 0)) (and (or (<= (+ (* (- 42) skoS) (* (- 235) skoC)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0)))))))))
(set-info :status unsat)
(check-sat)
