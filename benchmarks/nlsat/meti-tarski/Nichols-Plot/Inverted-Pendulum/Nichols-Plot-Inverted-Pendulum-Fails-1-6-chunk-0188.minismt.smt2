(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (+ (* 1421139257135874529181879533573505755800342281149054970154821684318646119498921850376815 pi) (* 14531075065584050344082604194055710735451433832410636019346684638210177601267302400 (* skoY pi)) (* 2938217405152478191114442083723887488098727382297251632447900182374252544000 (* skoY skoY pi)) (* (- 1251796679403874634551899023676096571916685492643143635491891445760000) (* skoY skoY skoY pi)) (* (- 73434952676111028526984040485439279129345378180214135193600000) (* skoY skoY skoY skoY pi))) 0)) (and (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (<= (* (- 1) skoY) 0)))))))
(set-info :status sat)
(check-sat)
