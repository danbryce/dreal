(set-logic QF_NRA)
(declare-fun skoA () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* (- 1) skoA) 0)) (and (not (<= (+ (* (- 120) skoA) (* 20 (* skoA skoA skoA)) (* (- 1) (* skoA skoA skoA skoA skoA))) 0)) (and (not (<= (+ (* (- 120) (* skoA skoA)) (* 20 (* skoA skoA skoA skoA)) (* (- 40000) (* skoA skoA skoA skoX)) (* 40000 (* skoA skoX skoX skoX)) (* 2000 (* skoA skoA skoA skoA skoA skoX)) (* (- 1) (* skoA skoA skoA skoA skoA skoA))) 0)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (+ (* (- 2) skoA) pi) 0)) (and (not (<= skoX 0)) (and (not (<= (+ skoA (* (- 1) skoX)) 0)) (or (not (<= (+ skoA (* (- 2000) skoX)) 0)) (not (<= (+ (* (- 1) skoA) (* 2000 skoX)) 0))))))))))))
(set-info :status unsat)
(check-sat)
