(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) (* skoX skoX)) 3)) (and (not (<= (+ (* (- 1) skoX) (* (- 1) skoY) (* (- 1) skoZ) (* skoX skoY skoZ)) 0)) (and (not (<= (+ (* (- 819) skoX) (* (- 819) skoY) (* (- 819) skoZ) (* 600 (* skoX skoX)) (* 450 (* skoX skoY)) (* 600 (* skoY skoY)) (* 450 (* skoX skoZ)) (* 450 (* skoY skoZ)) (* 819 (* skoX skoY skoZ)) (* (- 273) (* skoX skoX skoX)) (* (- 273) (* skoX skoX skoY)) (* (- 273) (* skoX skoY skoY)) (* (- 273) (* skoX skoX skoZ)) (* (- 273) (* skoY skoY skoZ)) (* (- 273) (* skoY skoY skoY)) (* 350 (* skoX skoX skoY skoY)) (* (- 300) (* skoX skoX skoY skoZ)) (* (- 300) (* skoX skoY skoY skoZ)) (* (- 91) (* skoX skoX skoX skoY skoY)) (* (- 91) (* skoX skoX skoY skoY skoY)) (* 273 (* skoX skoX skoX skoY skoZ)) (* (- 91) (* skoX skoX skoY skoY skoZ)) (* 273 (* skoX skoY skoY skoY skoZ)) (* (- 50) (* skoX skoX skoX skoY skoY skoY)) (* (- 150) (* skoX skoX skoX skoY skoY skoZ)) (* (- 150) (* skoX skoX skoY skoY skoY skoZ)) (* 91 (* skoX skoX skoX skoY skoY skoY skoZ))) (- 450))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status unsat)
(check-sat)
