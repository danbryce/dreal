(set-logic QF_NRA)
(declare-fun skoS3 () Real)
(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(assert (and (<= (+ (* (- 300) skoS3) (* (- 100) skoSX) (* 471 (* skoS3 skoX)) (* 157 (* skoX skoSX)) (* (- 800) (* skoS3 skoX skoX))) 0) (and (<= (+ (* (- 300) skoS3) (* (- 100) skoSX) (* 471 (* skoS3 skoX)) (* 157 (* skoX skoSX)) (* (- 800) (* skoS3 skoX skoX))) 0) (and (= (+ (* (- 80) (* skoX skoX)) (* skoSX skoSX)) 75) (and (= (* skoS3 skoS3) 3) (and (not (<= skoX 0)) (and (not (<= skoSX 0)) (not (<= skoS3 0)))))))))
(set-info :status sat)
(check-sat)
