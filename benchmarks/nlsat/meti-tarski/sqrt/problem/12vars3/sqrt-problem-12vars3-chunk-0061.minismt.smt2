(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(assert (and (<= (+ (* 24 skoX) (* (- 36) skoSX) (* 36 skoSMX) (* 6 (* skoX skoSX)) (* 6 (* skoX skoSMX)) (* 24 (* skoX skoX skoSX)) (* (- 24) (* skoX skoX skoSMX)) (* (- 12) (* skoX skoX skoX)) (* (- 3) (* skoX skoX skoX skoSX)) (* (- 3) (* skoX skoX skoX skoSMX))) 0) (and (not (<= (* skoX skoX) 2)) (and (<= (+ (* (- 12) skoX) (* 18 skoSX) (* (- 18) skoSMX) (* (- 3) (* skoX skoSX)) (* (- 3) (* skoX skoSMX)) (* (- 6) (* skoX skoX skoSX)) (* 6 (* skoX skoX skoSMX))) 0) (and (not (<= skoX 0)) (and (<= (* (- 1) skoSMX) 0) (and (<= (* (- 1) skoSX) 0) (and (<= skoX 1) (and (= (+ (* (- 1) skoX) (* skoSX skoSX)) 1) (= (+ skoX (* skoSMX skoSMX)) 1))))))))))
(set-info :status unsat)
(check-sat)
