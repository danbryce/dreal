(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* (- 1) skoX) 0) (and (<= (+ (* (- 4665901195008000000000000000000000000) skoS) (* 199065600000000000000000000000000000 skoC) (* 129245463101721600000000000000000000 (* skoX skoS)) (* (- 5514117120000000000000000000000000) (* skoX skoC)) (* (- 1790049663958844160000000000000000) (* skoX skoX skoS)) (* 76370522112000000000000000000000 (* skoX skoX skoC)) (* 16528125230553327744000000000000 (* skoX skoX skoX skoS)) (* (- 705154487500800000000000000000) (* skoX skoX skoX skoC)) (* (- 100150108818884070298800000000) (* skoX skoX skoX skoX skoS)) (* 4272795472700160000000000000 (* skoX skoX skoX skoX skoC)) (* 396308287754726963896680000 (* skoX skoX skoX skoX skoX skoS)) (* (- 16908062084827776000000000) (* skoX skoX skoX skoX skoX skoC)) (* (- 914811630900494741661503) (* skoX skoX skoX skoX skoX skoX skoS)) (* 39029443312477449600000 (* skoX skoX skoX skoX skoX skoX skoC))) 0) (and (<= skoX 0) (and (= (+ (* skoS skoS) (* skoC skoC)) 1) (and (<= skoX 75) (<= (* (- 1) skoX) 0)))))))
(set-info :status sat)
(check-sat)
