(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ (- 1.) (* skoY (* skoY (+ (/ 1. 3.) (* skoY (* skoY (+ (/ (- 2.) 45.) (* skoY (* skoY (+ (/ 1. 315.) (* skoY (* skoY (+ (/ (- 2.) 14175.) (* skoY (* skoY (+ (/ 2. 467775.) (* skoY (* skoY (+ (/ (- 4.) 42567525.) (* skoY (* skoY (+ (/ 1. 638512875.) (* skoY (* skoY (+ (/ (- 2.) 97692469875.) (* skoY (* skoY (+ (/ 2. 9280784638125.) (* skoY (* skoY (+ (/ (- 4.) 2143861251406875.) (* skoY (* skoY (+ (/ 60787. 4496002911110430720000.) (* skoY (* skoY (+ (/ (- 5611.) 67440043666656460800000.) (* skoY (* skoY (+ (/ 8839. 20084871186542415052800000.) (* skoY (* skoY (+ (/ (- 239.) 118357276634982088704000000.) (* skoY (* skoY (+ (/ 137. 16967699178391032236605440000.) (* skoY (* skoY (+ (/ (- 131.) 4666117274057533865066496000000.) (* skoY (* skoY (+ (/ 197. 2342536687741696298196664320000000.) (* skoY (* skoY (+ (/ (- 1.) 4685073375483392596393328640000000.) (* skoY (* skoY (+ (/ 47. 105176293377005638102417617715200000000.) (* skoY (* skoY (+ (/ (- 1.) 1367291813901073295331429030297600000000.) (* skoY (* skoY (/ 1. 1263377636044591724886240423994982400000000.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= skoY skoX))))))
(set-info :status sat)
(check-sat)
