(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 2. 45.) (* skoY (* skoY (+ (/ (- 1.) 315.) (* skoY (* skoY (+ (/ 2. 14175.) (* skoY (* skoY (+ (/ (- 2047.) 479001600.) (* skoY (* skoY (+ (/ 1. 10762752.) (* skoY (* skoY (+ (/ (- 30827.) 20922789888000.) (* skoY (* skoY (+ (/ 54647. 3201186852864000.) (* skoY (* skoY (+ (/ (- 8441.) 57926238289920000.) (* skoY (* skoY (+ (/ 2. 2143861251406875.) (* skoY (* skoY (+ (/ (- 4943.) 1079040698666503372800.) (* skoY (* skoY (+ (/ 2381. 134880087333312921600000.) (* skoY (* skoY (+ (/ (- 529.) 9711366287998530355200000.) (* skoY (* skoY (+ (/ 23. 169948910039974281216000000.) (* skoY (* skoY (/ (- 1.) 4078773840959382749184000000.)))))))))))))))))))))))))))))))))))))))))))))))) 0.) (and (not (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (/ 1. 3628800.))))))))))))))) 1.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))))))))))
(set-info :status unsat)
(check-sat)
