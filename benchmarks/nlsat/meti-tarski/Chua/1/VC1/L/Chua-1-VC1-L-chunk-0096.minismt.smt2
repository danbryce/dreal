(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0) (and (<= (+ (* 43776000000000000000 skoX) (* 415872000000000000 (* skoX skoX)) (* 2633856000000000 (* skoX skoX skoX)) (* 10946964000000 (* skoX skoX skoX skoX)) (* 29713188000 (* skoX skoX skoX skoX skoX)) (* 47045881 (* skoX skoX skoX skoX skoX skoX))) (- 2304000000000000000000)) (and (not (<= (+ (* 3108096000000000000000 skoX) (* 29526912000000000000 (* skoX skoX)) (* 187003776000000000 (* skoX skoX skoX)) (* 777234444000000 (* skoX skoX skoX skoX)) (* 2109636348000 (* skoX skoX skoX skoX skoX)) (* 3340257551 (* skoX skoX skoX skoX skoX skoX))) (- 159955200000000000000000))) (and (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0) (and (or (not (<= (+ (* (- 689) skoS) (* 1770 skoC)) 0)) (<= skoX 0)) (and (or (<= (+ (* 689 skoS) (* (- 1770) skoC)) 0) (<= skoX 0)) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 289) (<= (* (- 1) skoX) 0))))))))))
(set-info :status unsat)
(check-sat)
