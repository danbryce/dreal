(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (* 288 skoY) (* (- 576) (* skoY skoY pi skoX)) (* 192 (* skoY skoY skoY skoY pi skoX)) (* (- 24) (* skoY skoY skoY skoY skoY skoY pi skoX)) (* skoY skoY skoY skoY skoY skoY skoY skoY pi skoX)) 0)) (and (not (<= (+ skoY (* (- 1) skoX)) 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963))))))
(set-info :status sat)
(check-sat)
