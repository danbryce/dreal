(set-logic QF_NRA)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* (- 1) skoSX) (* (- 1) skoSMX)) 4) (and (not (<= skoX 0)) (and (<= (* (- 1) skoSMX) 0) (and (<= (* (- 1) skoSX) 0) (and (<= skoX 1) (and (= (+ (* (- 1) skoX) (* skoSX skoSX)) 1) (= (+ skoX (* skoSMX skoSMX)) 1))))))))
(set-info :status sat)
(check-sat)
