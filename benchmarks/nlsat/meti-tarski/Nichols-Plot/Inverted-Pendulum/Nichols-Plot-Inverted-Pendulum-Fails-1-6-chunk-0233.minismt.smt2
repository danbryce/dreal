(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* 577905454964822581574100495409876110551634229617467215155700855445497660883617192545088030974315 pi) 542038508653702546896624539949334927426922000109643764353707923238298996227330525297976868873728)) (and (<= (* (- 1) skoY) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825)))))))
(set-info :status sat)
(check-sat)
