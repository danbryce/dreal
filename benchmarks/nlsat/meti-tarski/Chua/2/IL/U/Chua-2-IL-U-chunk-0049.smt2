(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 106368.) 13.) (* skoX (+ (/ 920748. 8125.) (* skoX (+ (/ (- 21253933.) 20312500.) (* skoX (+ (/ 41211376087. 6500000000000.) (* skoX (+ (/ (- 1630793025157.) 65000000000000000.) (* skoX (/ 451729667968489. 7800000000000000000000.)))))))))))) (/ (- 3810048.) 13.)) (and (<= (* skoX (+ (+ (* skoC (/ 5743872. 40625.)) (* skoS (/ (- 1682883634137.) 507812500.))) (* skoX (+ (+ (* skoC (/ (- 49720392.) 25390625.)) (* skoS (/ 466158766655949. 10156250000000.))) (* skoX (+ (+ (* skoC (/ 573856191. 31738281250.)) (* skoS (/ (- 43041992787899291.) 101562500000000000.))) (* skoX (+ (+ (* skoC (/ (- 1112707154349.) 10156250000000000.)) (* skoS (/ 83458424015736725249. 32500000000000000000000.))) (* skoX (+ (+ (* skoC (/ 44031411679239. 101562500000000000000.)) (* skoS (/ (- 3302569064622724699139.) 325000000000000000000000000.))) (* skoX (+ (* skoC (/ (- 4065567011716401.) 4062500000000000000000000.)) (* skoS (/ 914811630900494741661503. 39000000000000000000000000000000.)))))))))))))) (+ (* skoC (/ 331776. 65.)) (* skoS (/ (- 24301568724.) 203125.)))) (and (<= skoX 0.) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX)))))))
(set-info :status unsat)
(check-sat)
