(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY 2019.))))) (* skoX (+ (* skoSXY (* skoSXY (* skoSXY (* skoSXY 115.)))) (* skoX (* skoSXY (* skoSXY skoSXY))))))) (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (* skoSXY (- 6001.))))))))) (and (not (<= skoY 1.)) (and (not (<= skoX (/ 3. 2.))) (and (not (<= skoSXY 0.)) (and (not (<= 2. skoX)) (not (<= (/ 33. 32.) skoY))))))))
(set-info :status sat)
(check-sat)
