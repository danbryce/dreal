(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoZ 0.)) (and (not (<= (* skoZ (* skoZ (* skoZ (/ 1. 6.)))) (+ (+ (/ 1. 10.) (* skoX (* skoX (* skoX (/ (- 1.) 6.))))) (* skoY (* skoY (* skoY (/ (- 1.) 6.))))))) (and (not (<= skoZ (/ 1. 10.))) (and (not (<= skoY (/ 1. 10.))) (and (not (<= skoX (/ 1. 10.))) (and (not (<= (/ 11. 10.) skoZ)) (and (not (<= (/ 11. 10.) skoY)) (not (<= (/ 11. 10.) skoX))))))))))
(set-info :status sat)
(check-sat)
