(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoR () Real)
(declare-fun skoE1 () Real)
(declare-fun skoE2 () Real)
(declare-fun skoE3 () Real)
(declare-fun skoEA1 () Real)
(declare-fun skoEA2 () Real)
(declare-fun skoEA3 () Real)
(assert (and (not (<= (* skoX (* skoX (/ (- 1.) 4.))) (+ 1. (* skoR (- 1.))))) (and (<= (* skoX (+ 1. (* skoX (/ (- 1.) 4.)))) skoR) (and (<= skoEA3 (/ 1. 85070591730234615865843651857942052864.)) (and (<= skoEA2 (/ 1. 85070591730234615865843651857942052864.)) (and (<= skoEA1 (/ 1. 85070591730234615865843651857942052864.)) (and (<= skoE3 (/ 1. 32.)) (and (<= skoE2 (/ 1. 32.)) (and (<= skoE1 (/ 1. 32.)) (and (<= (/ (- 1.) 32.) skoE3) (and (<= (/ (- 1.) 32.) skoE2) (and (<= (/ (- 1.) 32.) skoE1) (and (<= (/ (- 1.) 85070591730234615865843651857942052864.) skoEA3) (and (<= (/ (- 1.) 85070591730234615865843651857942052864.) skoEA2) (and (<= (/ (- 1.) 85070591730234615865843651857942052864.) skoEA1) (and (<= skoX 2.) (and (<= skoR 3.) (and (<= (/ 1. 2.) skoX) (<= 0. skoR)))))))))))))))))))
(set-info :status sat)
(check-sat)
