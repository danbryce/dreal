(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSXY () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (+ (- 1.) (* skoSXY (/ 18. 125.)))) (* skoSXY (/ (- 9.) 50.)))) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY))))))))
(set-info :status sat)
(check-sat)
