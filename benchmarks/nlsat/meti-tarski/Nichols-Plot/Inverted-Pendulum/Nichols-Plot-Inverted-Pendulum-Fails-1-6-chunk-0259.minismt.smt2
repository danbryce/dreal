(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* (- 5449593400282842414482545580309514434578008) pi) (* 861363605136608943560645725388800000 (* skoY pi))) (- 1815645390606319960080492382288725361643853))) (and (<= (* (- 1) skoY) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825)))))))
(set-info :status unsat)
(check-sat)
