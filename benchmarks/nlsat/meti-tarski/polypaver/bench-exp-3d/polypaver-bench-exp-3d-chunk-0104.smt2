(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ 2304. (* skoX (+ (- 2304.) (* skoX (+ 1152. (* skoX (+ (- 336.) (* skoX (+ 60. (* skoX (- 6.))))))))))) (* skoY (+ (+ (- 2304.) (* skoX (+ 2304. (* skoX (+ (- 1008.) (* skoX (+ 240. (* skoX (- 30.))))))))) (* skoY (+ (+ 1152. (* skoX (+ (- 1008.) (* skoX (+ 360. (* skoX (- 60.))))))) (* skoY (+ (+ (- 336.) (* skoX (+ 240. (* skoX (- 60.))))) (* skoY (+ (+ 60. (* skoX (- 30.))) (* skoY (- 6.))))))))))) (* skoZ (+ (+ (+ (- 1152.) (* skoX (+ 1152. (* skoX (+ (- 504.) (* skoX (+ 120. (* skoX (- 15.))))))))) (* skoY (+ (+ 1152. (* skoX (+ (- 1008.) (* skoX (+ 360. (* skoX (- 60.))))))) (* skoY (+ (+ (- 504.) (* skoX (+ 360. (* skoX (- 90.))))) (* skoY (+ (+ 120. (* skoX (- 60.))) (* skoY (- 15.))))))))) (* skoZ (+ (+ (+ 384. (* skoX (+ (- 336.) (* skoX (+ 120. (* skoX (- 20.))))))) (* skoY (+ (+ (- 336.) (* skoX (+ 240. (* skoX (- 60.))))) (* skoY (+ (+ 120. (* skoX (- 60.))) (* skoY (- 20.))))))) (* skoZ (+ (+ (+ (- 84.) (* skoX (+ 60. (* skoX (- 15.))))) (* skoY (+ (+ 60. (* skoX (- 30.))) (* skoY (- 15.))))) (* skoZ (+ (+ (+ 12. (* skoX (- 6.))) (* skoY (- 6.))) (* skoZ (- 1.)))))))))))) (+ (+ 2304. (* skoX (+ (- 2304.) (* skoX (+ 1152. (* skoX (+ (- 384.) (* skoX (+ 84. (* skoX (+ (- 12.) skoX))))))))))) (* skoY (+ (+ (- 2304.) (* skoX (+ 2304. (* skoX (+ (- 1152.) (* skoX (+ 336. (* skoX (+ (- 60.) (* skoX 6.)))))))))) (* skoY (+ (+ 1152. (* skoX (+ (- 1152.) (* skoX (+ 504. (* skoX (+ (- 120.) (* skoX 15.)))))))) (* skoY (+ (+ (- 384.) (* skoX (+ 336. (* skoX (+ (- 120.) (* skoX 20.)))))) (* skoY (+ (+ 84. (* skoX (+ (- 60.) (* skoX 15.)))) (* skoY (+ (+ (- 12.) (* skoX 6.)) skoY)))))))))))) (and (<= skoZ (+ (* skoX (- 1.)) (* skoY (- 1.)))) (and (<= 0. skoX) (and (<= 0. skoY) (and (<= 0. skoZ) (and (<= skoX 1.) (and (<= skoY 1.) (and (<= skoZ 1.) (and (<= skoZ (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.)))) (<= (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))) skoZ)))))))))))
(set-info :status unsat)
(check-sat)
