(set-logic QF_NRA)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 332640 skoZ) (* (- 75600) (* skoZ skoZ)) (* 10080 (* skoZ skoZ skoZ)) (* (- 840) (* skoZ skoZ skoZ skoZ)) (* 42 (* skoZ skoZ skoZ skoZ skoZ)) (* (- 1) (* skoZ skoZ skoZ skoZ skoZ skoZ))) 665280) (and (<= (* (- 1) skoX) 0) (and (<= (* (- 1) skoY) 0) (and (<= (* (- 1) skoZ) 0) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= (+ skoZ skoY skoX) 2) (<= (+ (* (- 1) skoZ) (* (- 1) skoY) (* (- 1) skoX)) (- 2)))))))))))
(set-info :status sat)
(check-sat)
