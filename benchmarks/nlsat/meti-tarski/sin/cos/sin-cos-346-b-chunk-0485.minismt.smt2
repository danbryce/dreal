(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3) 0) (and (<= (+ (* (- 188305108992000) (* skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 62768369664000 (* skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 31384184832000 (* skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 2615348736000) (* skoX skoX skoX skoX skoSQ3 skoSQ3)) (* 87178291200 (* skoX skoX skoX skoX skoX skoX)) (* (- 10461394944000) (* skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 871782912000 (* skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 29059430400) (* skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 518918400 (* skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 5765760) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* 43680 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* (- 240) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3 skoSQ3)) 0) (and (not (<= skoSQ3 0)) (and (not (<= skoX 0)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (+ (* (- 10000000) skoX) (* 5000000 pi)) 1)) (= (* skoSQ3 skoSQ3) 3)))))))))
(set-info :status unsat)
(check-sat)
