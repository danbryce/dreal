(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 1746562500000000000000000000000000000000000000000000000000) skoX) (* 209587500000000000000000000000000000000000000000000000 (* skoX skoX)) (* (- 16767000000000000000000000000000000000000000000000) (* skoX skoX skoX)) (* 990300937500000000000000000000000000000000000 (* skoX skoX skoX skoX)) (* (- 45270900000000000000000000000000000000000) (* skoX skoX skoX skoX skoX)) (* 1641070125000000000000000000000000000 (* skoX skoX skoX skoX skoX skoX)) (* (- 47534445000000000000000000000000) (* skoX skoX skoX skoX skoX skoX skoX)) (* 1094989893750000000000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 19692841500000000000000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 264834765000000000 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* (- 2444628600000) (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX)) (* 12223143 (* skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX skoX))) (- 7277343750000000000000000000000000000000000000000000000000000))) (and (not (<= skoX 0)) (not (<= (+ (* 235 skoC) (* 42 skoS)) 0)))))
(set-info :status sat)
(check-sat)
