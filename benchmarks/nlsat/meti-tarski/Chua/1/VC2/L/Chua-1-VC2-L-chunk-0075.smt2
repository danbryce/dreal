(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 78479622144. 1953125.) (* skoX (+ (/ (- 29429858304.) 6103515625.) (* skoX (+ (/ 7357464576. 19073486328125.) (* skoX (+ (/ (- 1357969536.) 59604644775390625.) (* skoX (+ (/ 193995648. 186264514923095703125.) (* skoX (+ (/ (- 43952139.) 1164153218269348144531250.) (* skoX (+ (/ 31827411. 29103830456733703613281250000.) (* skoX (+ (/ (- 586533717.) 23283064365386962890625000000000000.) (* skoX (+ (/ 131856417. 291038304567337036132812500000000000000.) (* skoX (+ (/ (- 177324147.) 29103830456733703613281250000000000000000000.) (* skoX (+ (/ 40920957. 727595761418342590332031250000000000000000000000.) (* skoX (/ (- 40920957.) 145519152283668518066406250000000000000000000000000000.)))))))))))))))))))))))) (/ 104639496192. 625.)) (and (not (<= skoX 0.)) (and (<= skoS (* skoC (/ 3. 13.))) (and (or (not (<= (* skoC (/ 3. 13.)) skoS)) (not (<= skoS (* skoC (/ 3. 13.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)
