(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (= (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC skoC)))))))))) 0.)) (and (not (= (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC skoC))))))))) 0.)) (and (not (= (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC skoC)))))))) 0.)) (and (not (= (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC skoC))))))) 0.)) (and (not (= (* skoC (* skoC (* skoC (* skoC (* skoC (* skoC skoC)))))) 0.)) (and (not (= (* skoC (* skoC (* skoC (* skoC (* skoC skoC))))) 0.)) (and (not (= (* skoC (* skoC (* skoC (* skoC skoC)))) 0.)) (and (not (= (* skoC (* skoC (* skoC skoC))) 0.)) (and (not (= (* skoC (* skoC skoC)) 0.)) (and (not (= (* skoC skoC) 0.)) (and (not (= skoC 0.)) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.))))))))))))))))
(set-info :status sat)
(check-sat)
