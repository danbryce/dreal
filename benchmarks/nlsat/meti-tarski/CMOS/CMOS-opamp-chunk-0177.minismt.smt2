(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* (- 90720000000000000000000) (* skoX skoX)) (* (- 2721690719244) (* skoX skoX skoX skoX)) (* 2721645360000000000000000000 (* skoY skoY skoX skoX)) (* 2721645360000 (* skoY skoY skoX skoX skoX skoX)) (* (- 793803780000000000000000000) (* skoY skoY skoY skoY skoX skoX)) (* (- 793803780000) (* skoY skoY skoY skoY skoX skoX skoX skoX)) (* 60480126000000000000000000 (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* 60480126000 (* skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 1957502250000000000000000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 1957502250) (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* 34500025000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 34500025 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 375000000000000000000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 375000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX))) (- 733320000000000000000000000000000)) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= skoX 120) (<= (* (- 1) skoX) (- 100)))))))))
(set-info :status unsat)
(check-sat)
