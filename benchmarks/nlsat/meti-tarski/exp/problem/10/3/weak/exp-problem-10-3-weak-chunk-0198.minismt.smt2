(set-logic QF_NRA)
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (<= (+ (* 48 skoC) (* (- 1) skoCM1) (* (- 1248) (* skoC skoC)) (* 48 (* skoC skoCM1)) (* 22272 (* skoC skoC skoC)) (* (- 1248) (* skoC skoC skoCM1)) (* (- 297216) (* skoC skoC skoC skoC)) (* 22272 (* skoC skoC skoC skoCM1)) (* 3096576 (* skoC skoC skoC skoC skoC)) (* (- 297216) (* skoC skoC skoC skoC skoCM1)) (* (- 25657344) (* skoC skoC skoC skoC skoC skoC)) (* 3096576 (* skoC skoC skoC skoC skoC skoCM1)) (* 169869312 (* skoC skoC skoC skoC skoC skoC skoC)) (* (- 25657344) (* skoC skoC skoC skoC skoC skoC skoCM1)) (* (- 891813888) (* skoC skoC skoC skoC skoC skoC skoC skoC)) (* 169869312 (* skoC skoC skoC skoC skoC skoC skoC skoCM1)) (* 3623878656 (* skoC skoC skoC skoC skoC skoC skoC skoC skoC)) (* (- 891813888) (* skoC skoC skoC skoC skoC skoC skoC skoC skoCM1)) (* (- 10871635968) (* skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC)) (* 3623878656 (* skoC skoC skoC skoC skoC skoC skoC skoC skoC skoCM1)) (* 21743271936 (* skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC)) (* (- 10871635968) (* skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC skoCM1)) (* 21743271936 (* skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC skoCM1)) (* (- 21743271936) (* skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC skoC))) 1) (and (= (+ (* (- 1) skoX) (* skoCM1 skoCM1 skoCM1)) (- 1)) (and (= (+ (* (- 1) skoX) (* skoC skoC skoC)) 0) (and (not (<= skoX 1)) (and (not (<= skoCM1 0)) (not (<= skoC 0))))))))
(set-info :status sat)
(check-sat)
