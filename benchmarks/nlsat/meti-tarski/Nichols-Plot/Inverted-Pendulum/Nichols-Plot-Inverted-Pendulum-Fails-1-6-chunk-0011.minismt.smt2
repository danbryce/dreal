(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600)) (and (not (<= (* 5000000 pi) 15707963)) (not (<= (* (- 10000000) pi) (- 31415927))))))
(set-info :status sat)
(check-sat)
