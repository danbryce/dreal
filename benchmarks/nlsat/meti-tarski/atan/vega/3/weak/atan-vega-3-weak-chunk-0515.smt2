(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ 189. (* skoX (+ (/ 25137. 50.) (* skoX (+ 588. (* skoX (+ (/ 2793. 5.) (* skoX (+ 339. (* skoX (+ (/ 1197. 10.) (* skoX (/ 128. 5.))))))))))))) (* skoY (+ (+ (/ 25137. 50.) (* skoX (+ 378. (* skoX (+ (/ 2793. 50.) (* skoX (+ (- 84.) (* skoX (+ (/ (- 4389.) 10.) (* skoX (+ (/ (- 1342.) 5.) (* skoX (+ (/ (- 1197.) 10.) (* skoX (/ (- 128.) 5.))))))))))))))) (* skoY (+ (+ 378. (* skoX (+ (/ (- 25137.) 50.) (* skoX (+ (- 147.) (* skoX (+ (/ (- 2793.) 5.) (* skoX (+ (- 414.) (* skoX (+ (/ (- 1197.) 10.) (* skoX (/ (- 353.) 5.))))))))))))) (* skoY (* skoX (+ (- 378.) (* skoX (* skoX (+ (- 420.) (* skoX (* skoX (- 90.)))))))))))))) (* skoZ (+ (+ (/ 25137. 100.) (* skoX (+ 189. (* skoX (+ (/ 2793. 10.) (* skoX (+ 147. (* skoX (+ (/ 1197. 20.) (* skoX (/ 64. 5.))))))))))) (* skoY (+ (+ 189. (* skoX (+ (/ (- 25137.) 50.) (* skoX (+ (- 168.) (* skoX (+ (/ (- 2793.) 5.) (* skoX (+ (- 249.) (* skoX (+ (/ (- 1197.) 10.) (* skoX (/ (- 128.) 5.))))))))))))) (* skoY (+ (* skoX (+ (- 378.) (* skoX (+ (/ 25137. 100.) (* skoX (+ (- 231.) (* skoX (+ (/ 2793. 10.) (* skoX (+ 57. (* skoX (+ (/ 1197. 20.) (* skoX (/ 64. 5.)))))))))))))) (* skoY (* skoX (* skoX (+ 189. (* skoX (* skoX (+ 210. (* skoX (* skoX 45.))))))))))))))))) (+ (+ (/ (- 8379.) 100.) (* skoX (+ (- 252.) (* skoX (+ (/ (- 34447.) 100.) (* skoX (+ (- 448.) (* skoX (+ (/ (- 1197.) 4.) (* skoX (+ (/ (- 2944.) 15.) (* skoX (+ (/ (- 1197.) 20.) (* skoX (/ (- 64.) 5.))))))))))))))) (* skoY (+ (+ (- 252.) (* skoX (+ (/ (- 8379.) 25.) (* skoX (+ (- 532.) (* skoX (+ (/ (- 1862.) 5.) (* skoX (+ (- 256.) (* skoX (+ (/ (- 399.) 5.) (* skoX (/ (- 256.) 15.))))))))))))) (* skoY (+ (+ (/ (- 25137.) 100.) (* skoX (+ (- 252.) (* skoX (+ (/ (- 36309.) 100.) (* skoX (+ (- 280.) (* skoX (+ (/ (- 3059.) 20.) (* skoX (+ (/ (- 384.) 5.) (* skoX (+ (/ (- 399.) 20.) (* skoX (/ (- 64.) 15.))))))))))))))) (* skoY (+ (- 189.) (* skoX (* skoX (+ (- 273.) (* skoX (* skoX (+ (- 115.) (* skoX (* skoX (- 15.))))))))))))))))) (and (not (<= 0. skoX)) (and (or (not (<= 0. skoX)) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
