(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ (+ (+ (- 189.) (* skoX (+ (/ (- 14931.) 25.) (* skoX (+ (- 588.) (* skoX (+ (/ (- 3318.) 5.) (* skoX (+ (- 339.) (* skoX (+ (/ (- 711.) 5.) (* skoX (/ (- 128.) 5.))))))))))))) (* skoY (+ (+ (/ (- 14931.) 25.) (* skoX (+ (- 378.) (* skoX (+ (/ (- 1659.) 25.) (* skoX (+ 84. (* skoX (+ (/ 2607. 5.) (* skoX (+ (/ 1342. 5.) (* skoX (+ (/ 711. 5.) (* skoX (/ 128. 5.))))))))))))))) (* skoY (+ (+ (- 378.) (* skoX (+ (/ 14931. 25.) (* skoX (+ 147. (* skoX (+ (/ 3318. 5.) (* skoX (+ 414. (* skoX (+ (/ 711. 5.) (* skoX (/ 353. 5.))))))))))))) (* skoY (* skoX (+ 378. (* skoX (* skoX (+ 420. (* skoX (* skoX 90.))))))))))))) (* skoZ (+ (+ (/ (- 14931.) 50.) (* skoX (+ (- 189.) (* skoX (+ (/ (- 1659.) 5.) (* skoX (+ (- 147.) (* skoX (+ (/ (- 711.) 10.) (* skoX (/ (- 64.) 5.))))))))))) (* skoY (+ (+ (- 189.) (* skoX (+ (/ 14931. 25.) (* skoX (+ 168. (* skoX (+ (/ 3318. 5.) (* skoX (+ 249. (* skoX (+ (/ 711. 5.) (* skoX (/ 128. 5.))))))))))))) (* skoY (+ (* skoX (+ 378. (* skoX (+ (/ (- 14931.) 50.) (* skoX (+ 231. (* skoX (+ (/ (- 1659.) 5.) (* skoX (+ (- 57.) (* skoX (+ (/ (- 711.) 10.) (* skoX (/ (- 64.) 5.)))))))))))))) (* skoY (* skoX (* skoX (+ (- 189.) (* skoX (* skoX (+ (- 210.) (* skoX (* skoX (- 45.)))))))))))))))))) (+ (+ (/ 4977. 50.) (* skoX (+ 252. (* skoX (+ (/ 20461. 50.) (* skoX (+ 448. (* skoX (+ (/ 711. 2.) (* skoX (+ (/ 2944. 15.) (* skoX (+ (/ 711. 10.) (* skoX (/ 64. 5.))))))))))))))) (* skoY (+ (+ 252. (* skoX (+ (/ 9954. 25.) (* skoX (+ 532. (* skoX (+ (/ 2212. 5.) (* skoX (+ 256. (* skoX (+ (/ 474. 5.) (* skoX (/ 256. 15.))))))))))))) (* skoY (+ (+ (/ 14931. 50.) (* skoX (+ 252. (* skoX (+ (/ 21567. 50.) (* skoX (+ 280. (* skoX (+ (/ 1817. 10.) (* skoX (+ (/ 384. 5.) (* skoX (+ (/ 237. 10.) (* skoX (/ 64. 15.))))))))))))))) (* skoY (+ 189. (* skoX (* skoX (+ 273. (* skoX (* skoX (+ 115. (* skoX (* skoX 15.))))))))))))))))) (and (or (not (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (<= 0. skoY)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
