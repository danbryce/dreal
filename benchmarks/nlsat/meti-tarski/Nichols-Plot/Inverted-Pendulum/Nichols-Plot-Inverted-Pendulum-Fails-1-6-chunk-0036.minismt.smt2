(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 90819219159900314650516276212848192096571461452566475120916778988813610007920640 skoY) (* 97940580171749273037148069457462916269957579409908387748263339412475084800 (* skoY skoY)) (* 15647458492548432931898737795951207148958568658039295443648643072000 (* skoY skoY skoY)) (* 312489160323876717136102299938039485656788843320060149760000 (* skoY skoY skoY skoY))) 0) (and (= (* 295147905179352825856 (* skoY skoY)) 1325421053866224634595698711821825) (and (= (+ (* skoY skoY) (* (- 15328072984) (* skoX skoX)) (* (- 129098541721) (* skoX skoX skoX skoX)) (* (- 21404723599) (* skoX skoX skoX skoX skoX skoX)) (* (- 1024027285) (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 15132100) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) 277555600) (and (not (<= (* 5000000 pi) 15707963)) (and (not (<= (* (- 10000000) pi) (- 31415927))) (<= (* (- 1) skoY) 0)))))))
(set-info :status unsat)
(check-sat)
