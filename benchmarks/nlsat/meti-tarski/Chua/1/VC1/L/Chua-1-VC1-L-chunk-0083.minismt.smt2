(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 3108096000000000000000) skoX) (* (- 29526912000000000000) (* skoX skoX)) (* (- 187003776000000000) (* skoX skoX skoX)) (* (- 777234444000000) (* skoX skoX skoX skoX)) (* (- 2109636348000) (* skoX skoX skoX skoX skoX)) (* (- 3340257551) (* skoX skoX skoX skoX skoX skoX))) 159955200000000000000000)) (and (not (<= (+ (* 43776000000000000000 skoX) (* 415872000000000000 (* skoX skoX)) (* 2633856000000000 (* skoX skoX skoX)) (* 10946964000000 (* skoX skoX skoX skoX)) (* 29713188000 (* skoX skoX skoX skoX skoX)) (* 47045881 (* skoX skoX skoX skoX skoX skoX))) (- 2304000000000000000000))) (not (<= (+ (* (- 1770) skoC) (* 689 skoS)) 0)))))
(set-info :status sat)
(check-sat)
