(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 354180071259563920828841622025110189960239618912941679848313713474982431218920152161893843380627046400 skoY) (* 679026154944561518873529373639481061493504175238846496816711535821664755917127336548108337152000 (* skoY skoY)) (* 244090095254589311785217173309398176587377318735836213367225279171569726864181040250880000 (* skoY skoY skoY)) (* 19498504232059232347399271394882943156573417785501687194060739574669457856921600000 (* skoY skoY skoY skoY)) (* 233638116424441564739602807863833201595327239797089780403456596298956800000 (* skoY skoY skoY skoY skoY))) 0) (and (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (<= (* (- 1) skoY) 0)))))))
(set-info :status unsat)
(check-sat)
