(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (+ (* skoC (/ (- 306432.) 125.)) (* skoS (/ 12096. 25.))) (* skoX (+ (+ (* skoC (/ 536256. 15625.)) (* skoS (/ (- 21168.) 3125.))) (* skoX (+ (+ (* skoC (/ (- 625632.) 1953125.)) (* skoS (/ 24696. 390625.))) (* skoX (+ (+ (* skoC (/ 957999. 488281250.)) (* skoS (/ (- 151263.) 390625000.))) (* skoX (+ (+ (* skoC (/ (- 957999.) 122070312500.)) (* skoS (/ 151263. 97656250000.))) (* skoX (+ (* skoC (/ 2235331. 122070312500000.)) (* skoS (/ (- 352947.) 97656250000000.)))))))))))))) (+ (* skoC (- 87552.)) (* skoS 17280.)))) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
