(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (<= (+ (* 3 skoS3) skoSX) 0) (and (not (<= (+ (* (- 5775) (* skoX skoS3)) (* 1155 (* skoX skoSX)) (* (- 9030) (* skoX skoX skoX skoS3)) (* 1190 (* skoX skoX skoX skoSX)) (* (- 3507) (* skoX skoX skoX skoX skoX skoS3)) (* 231 (* skoX skoX skoX skoX skoX skoSX)) (* (- 200) (* skoX skoX skoX skoX skoX skoX skoX skoS3))) 0)) (and (<= (+ (* (- 300) skoS3) (* (- 100) skoSX) (* 471 (* skoX skoS3)) (* 157 (* skoX skoSX)) (* (- 800) (* skoX skoX skoS3))) 0) (and (= (+ (* (- 80) (* skoX skoX)) (* skoSX skoSX)) 75) (and (= (* skoS3 skoS3) 3) (and (not (<= skoX 0)) (and (not (<= skoSX 0)) (not (<= skoS3 0))))))))))
(set-info :status unsat)
(check-sat)
