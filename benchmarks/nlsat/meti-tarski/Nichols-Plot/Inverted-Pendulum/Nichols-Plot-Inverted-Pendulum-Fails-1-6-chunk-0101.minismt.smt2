(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* 51070206540657556569455016548742010931551934169662944596180236547108511690128670146181035372576768 skoY) (* 440172580411670152495949690193641113644309662953646311653784577172614401829256631029718995760754775052500 pi) (* (- 196235374691208904004940781953876201423968444229080877651970054056792461910455013457368849999462400) (* skoY pi))) 0)) (and (not (<= skoY 0)) (and (<= (* (- 1) skoY) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825))))))))
(set-info :status sat)
(check-sat)
