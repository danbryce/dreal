(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (* 3139139565556413757031246886608524785790584795902482097418859414134156981043185 pi) 2944313118675309517893327913770056693331415133307224689027900572059989397946232) (and (<= (* (- 1) skoY) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825)))))))
(set-info :status unsat)
(check-sat)
