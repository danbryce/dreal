(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ (- 1.) (* skoY (* skoY (+ (/ 7. 24.) (* skoY (* skoY (+ (/ (- 1.) 45.) (* skoY (* skoY (/ 1. 1440.)))))))))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= skoY skoX))))))
(set-info :status sat)
(check-sat)