(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoX skoX) (- 3)) (and (<= (+ (* (- 13860) skoZ) (* (- 1155) (* skoX skoX)) (* 3465 (* skoY skoX)) (* (- 4725) (* skoY skoY)) (* (- 4620) (* skoX skoX skoX)) (* (- 13860) (* skoY skoX skoX)) (* (- 13860) (* skoY skoY skoX)) (* (- 4620) (* skoY skoY skoY)) (* (- 4620) (* skoX skoX skoZ)) (* 13860 (* skoY skoX skoZ)) (* (- 18900) (* skoY skoY skoZ)) (* 1155 (* skoY skoX skoX skoX)) (* (- 1575) (* skoY skoY skoX skoX)) (* 4725 (* skoY skoY skoY skoX)) (* (- 1575) (* skoY skoY skoY skoY)) (* (- 10920) (* skoY skoY skoX skoX skoX)) (* (- 20440) (* skoY skoY skoY skoX skoX)) (* (- 14280) (* skoY skoY skoY skoY skoX)) (* (- 3528) (* skoY skoY skoY skoY skoY)) (* 4620 (* skoY skoX skoX skoX skoZ)) (* (- 6300) (* skoY skoY skoX skoX skoZ)) (* 18900 (* skoY skoY skoY skoX skoZ)) (* (- 6300) (* skoY skoY skoY skoY skoZ)) (* 1575 (* skoY skoY skoY skoX skoX skoX)) (* (- 525) (* skoY skoY skoY skoY skoX skoX)) (* 1575 (* skoY skoY skoY skoY skoY skoX)) (* (- 75) (* skoY skoY skoY skoY skoY skoY)) (* (- 6860) (* skoY skoY skoY skoY skoX skoX skoX)) (* (- 7476) (* skoY skoY skoY skoY skoY skoX skoX)) (* (- 2772) (* skoY skoY skoY skoY skoY skoY skoX)) (* 6300 (* skoY skoY skoY skoX skoX skoX skoZ)) (* (- 2100) (* skoY skoY skoY skoY skoX skoX skoZ)) (* 6300 (* skoY skoY skoY skoY skoY skoX skoZ)) (* (- 300) (* skoY skoY skoY skoY skoY skoY skoZ)) (* (- 300) (* skoY skoY skoY skoY skoY skoY skoY)) (* 525 (* skoY skoY skoY skoY skoY skoX skoX skoX)) (* (- 25) (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* 75 (* skoY skoY skoY skoY skoY skoY skoY skoX)) (* (- 1024) (* skoY skoY skoY skoY skoY skoY skoX skoX skoX)) (* 2100 (* skoY skoY skoY skoY skoY skoX skoX skoX skoZ)) (* (- 100) (* skoY skoY skoY skoY skoY skoY skoX skoX skoZ)) (* 300 (* skoY skoY skoY skoY skoY skoY skoY skoX skoZ)) (* (- 400) (* skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 25 (* skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX)) (* 100 (* skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoZ))) 3465) (and (not (<= (* (- 1) skoY) 0)) (and (or (not (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (<= (* (- 1) skoY) 0)) (and (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1) (and (not (<= (* (- 1) skoX) 0)) (and (or (not (<= (* (- 1) skoX) 0)) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (<= (* (- 1) skoY) 0) (<= (+ skoY skoX skoZ (* skoY skoX) (* (- 1) (* skoY skoX skoZ))) 1)) (and (or (not (<= (* (- 1) skoY) 0)) (<= (+ (* (- 1) skoY) (* (- 1) skoX) (* (- 1) skoZ) (* skoY skoX skoZ)) 0)) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ skoY (* (- 1) skoX)) 0)))))))))))))))
(set-info :status unsat)
(check-sat)
