(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 360) (* skoY skoY)) (* 30 (* skoY skoY skoY skoY)) (* (- 1) (* skoY skoY skoY skoY skoY skoY))) (- 720)) (and (not (<= (+ (* (- 809280523999877529600000) (* skoY skoY)) (* 269760174666625843200000 (* skoY skoY skoY skoY)) (* (- 35968023288883445760000) (* skoY skoY skoY skoY skoY skoY)) (* 2549073079067074560000 (* skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 103925464115945472000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 2510619711215616000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 38023376928768000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 384821143660800 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 2752808889600) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 14568301440 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 59155200) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* 189780 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* (- 492) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY)) 0)) (and (<= (+ (* 10 skoY) (* (- 5) pi)) (- 2)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (* (- 10) skoX) (- 1)) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))
(set-info :status unsat)
(check-sat)
