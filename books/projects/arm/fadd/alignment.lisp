(in-package "RTL")

(include-book "prelim")

(local-defthm far-1
  (implies (equal (mulovfl) 0)
           (equal (expap1) (+ (expa) 1)))
  :hints (("Goal" :in-theory (enable mulovfl expap1 expa expnt cat-0 bvecp)
           :use ((:instance bits-bounds (x (opaz)) (i 115) (j 105))))))

(local-defthm far-2
  (implies (equal (mulovfl) 0)
           (equal (expbp1) (+ (expb) 1)))
  :hints (("Goal" :in-theory (enable mulovfl expbp1 expb expnt cat-0 bvecp)
                  :use ((:instance bits-bounds (x (opbz)) (i 115) (j 105))))))

(defthmd far-rewrite
  (implies (equal (mulovfl) 0)
           (equal (far)
                  (if (and (= (usa) 1)
                           (or (= (expa) (expb))
                               (= (expa) (1+ (expb)))
                               (= (1+ (expa)) (expb))))
                      0
                    1)))
  :hints (("Goal" :in-theory (enable mulovfl far-1 far-2 isnear isfar-lemma))))

(defund bp () (val (signb) (expb) (sigb)))

(defund l () (if (>= (abs (b)) (abs (a))) (bp) (a)))

(defund s () (if (>= (abs (b)) (abs (a))) (a) (bp)))

(in-theory (disable (bp) (l) (s)))

(defthm siga-bounds
  (and (< (siga) (expt 2 107))
       (>= (siga) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat siga)
                  :use ((:instance bits-bounds (x (* 2 (bits (fraca) 104 0))) (i 105) (j 0))))))

(defthm siga-expa-0
  (iff (= (expa) 0)
       (< (siga) (expt 2 106)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat siga)
                  :use ((:instance bits-bounds (x (* 2 (bits (fraca) 104 0))) (i 105) (j 0))))))

(defthm sigb-bounds
  (and (< (sigb) (expt 2 107))
       (>= (sigb) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat sigb)
                  :use ((:instance bits-bounds (x (* 2 (bits (fracb) 104 0))) (i 105) (j 0))))))

(defthm sigb-expb-0
  (iff (= (expb) 0)
       (< (sigb) (expt 2 106)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat sigb)
                  :use ((:instance bits-bounds (x (* 2 (bits (fracb) 104 0))) (i 105) (j 0))))))

(defthm fraca-104-0
  (equal (bits (fraca) 104 0) (fraca))
  :hints (("Goal" :use (bvecp-fraca))))

(defthm fracb-104-0
  (equal (bits (fracb) 104 0) (fracb))
  :hints (("Goal" :use (bvecp-fracb))))

(defthm fraca-105-0
  (equal (bits (* 2 (fraca)) 105 0) (* 2 (fraca)))
  :hints (("Goal" :in-theory (enable bvecp) :use (bvecp-fraca))))

(defthm fracb-105-0
  (equal (bits (* 2 (fracb)) 105 0) (* 2 (fracb)))
  :hints (("Goal" :in-theory (enable bvecp) :use (bvecp-fracb))))

(local-defthm opbgeopa-1
  (implies (and (<= (expa) (expb)) (<= (siga) (sigb)))
           (equal (opbgeopa) 1))
  :hints (("Goal" :in-theory (enable cat siga sigb opbgeopa))))

(local-defthmd opbgeopa-2
  (equal (bits (fraca) 51 0) 0)
  :hints (("Goal" :in-theory (enable fraca frac opax checkdenorm opaz))))

(local-defthmd opbgeopa-3
  (equal (bits (siga) 52 0) 0)
  :hints (("Goal" :in-theory (enable opbgeopa-2 siga))))

(local-defthmd opbgeopa-4
  (integerp (* (expt 2 -53) (siga)))
  :hints (("Goal" :in-theory (enable bits)
                  :use (opbgeopa-3 (:instance mod-def (x (siga)) (y (expt 2 53)))))))

(local-defthmd opbgeopa-5
  (implies (<= (siga) (sigb))
           (<= (chop (siga) -53) (chop (sigb) -53)))
  :hints (("Goal" :in-theory (enable chop))))

(local-defthmd opbgeopa-6
  (equal (chop (siga) -53) (siga))
  :hints (("Goal" :use (opbgeopa-4) :in-theory (enable chop))))

(local-defthmd opbgeopa-7
  (implies (<= (siga) (sigb))
           (<= (siga) (chop (sigb) -53)))
  :hints (("Goal" :use (opbgeopa-6 opbgeopa-5))))

(local-defthmd opbgeopa-8
  (equal (abs (a)) (absval (expa) (siga)))
  :hints (("Goal" :in-theory (enable a val absval))))

(local-defthmd opbgeopa-9
  (implies (and (<= (expa) (expb)) (<= (siga) (sigb)))
           (<= (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :in-theory (enable absval) :nonlinearp t)))

(local-defthmd opbgeopa-10
  (implies (and (<= (expa) (expb)) (<= (siga) (sigb)))
           (<= (absval (expa) (siga)) (absval (expb) (chop (sigb) -53))))
  :hints (("Goal" :in-theory (enable absval) :use (opbgeopa-7) :nonlinearp t)))

(local-defthm rat-abs
  (implies (rationalp x) (rationalp (abs x)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd opbgeopa-11
  (implies (and (equal (mulovfl) 0) (> (expb) 0))
           (equal (abs (b)) (absval (expb) (sigb))))
  :hints (("Goal" :in-theory (enable absval val) :use (expb-pos-b))))

(local-defthmd opbgeopa-12
  (implies (and (equal (mulovfl) 0) (<= (expa) (expb)) (<= (siga) (sigb)))
           (<= (abs (a)) (abs (b))))
  :hints (("Goal" :in-theory (e/d (opbgeopa-8 opbgeopa-11) (abs))
                  :use (expb-0-b expb-pos-b opbgeopa-9 opbgeopa-10))))

(local-defthm opbgeopa-13
  (implies (and (<= (expb) (expa)) (< (sigb) (siga)))
           (equal (opbgeopa) 0))
  :hints (("Goal" :in-theory (enable cat siga sigb opbgeopa))))

(local-defthmd opbgeopa-14
  (implies (< (sigb) (siga))
           (< (chop (sigb) -53) (chop (siga) -53)))
  :hints (("Goal" :in-theory (enable chop) :use (opbgeopa-6))))

(local-defthmd opbgeopa-15
  (implies (< (sigb) (siga))
           (<= (+ (expt 2 53) (chop (sigb) -53)) (chop (siga) -53)))
  :hints (("Goal" :in-theory (enable chop) :use (opbgeopa-14))))

(local-defthmd opbgeopa-16
  (implies (< (sigb) (siga))
           (<= (absval (expb) (+ (expt 2 53) (chop (sigb) -53)))
	       (absval (expb) (chop (siga) -53))))
  :hints (("Goal" :in-theory (enable absval) :use (opbgeopa-15) :nonlinearp t)))

(local-defthmd opbgeopa-17
  (implies (<= (expb) (expa))
           (<= (absval (expb) (chop (siga) -53))
	       (absval (expa) (chop (siga) -53))))
  :hints (("Goal" :in-theory (enable chop absval) :nonlinearp t)))

(local-defthmd opbgeopa-18
  (implies (and (<= (expb) (expa)) (< (sigb) (siga)))
           (< (absval (expb) (sigb)) (absval (expa) (siga))))
  :hints (("Goal" :in-theory (enable absval) :nonlinearp t)))

(local-defthmd opbgeopa-19
  (implies (and (equal (mulovfl) 0) (<= (expb) (expa)) (< (sigb) (siga)))
           (< (abs (b)) (abs (a))))
  :hints (("Goal" :use (expb-0-b opbgeopa-16 opbgeopa-17 opbgeopa-18)
                  :in-theory (e/d (opbgeopa-6 opbgeopa-8 opbgeopa-11) (abs)))))

(local-defthm opbgeopa-20
  (implies (and (> (expb) 0) (< (expb) (expa)))
           (equal (opbgeopa) 0))
  :hints (("Goal" :in-theory (enable opbgeopa))))

(local-defthmd opbgeopa-21
  (implies (and (equal (mulovfl) 0) (> (expb) 0) (< (expb) (expa)))
           (< (abs (b)) (absval (expb) (expt 2 107))))
  :hints (("Goal" :in-theory (e/d (opbgeopa-11 absval bvecp) (abs)) :use (bvecp-sigb) :nonlinearp t)))

(local-defthmd opbgeopa-22
  (implies (and (> (expb) 0) (< (expb) (expa)))
           (<= (absval (expb) (expt 2 107)) (absval (expa) (expt 2 106))))
  :hints (("Goal" :in-theory (enable absval) :nonlinearp t)))

(local-defthmd opbgeopa-23
  (implies (and (equal (mulovfl) 0) (> (expb) 0) (< (expb) (expa)))
           (<= (absval (expa) (expt 2 106)) (abs (a))))
  :hints (("Goal" :in-theory (e/d (opbgeopa-8 absval bvecp) (abs)) :use (bvecp-siga-0) :nonlinearp t)))

(local-defthmd opbgeopa-24
  (implies (and (equal (mulovfl) 0) (> (expb) 0) (< (expb) (expa)))
           (< (abs (b)) (abs (a))))
  :hints (("Goal" :use (opbgeopa-21 opbgeopa-22 opbgeopa-23))))

(local-defthm opbgeopa-25
  (implies (and (equal (mulovfl) 0) (> (expa) 0) (< (expa) (expb)))
           (equal (opbgeopa) 1))
  :hints (("Goal" :in-theory (enable opbgeopa))))

(local-defthmd opbgeopa-26
  (implies (and (equal (mulovfl) 0) (> (expa) 0) (< (expa) (expb)))
           (< (abs (a)) (absval (expa) (expt 2 107))))
  :hints (("Goal" :in-theory (e/d (opbgeopa-8 absval bvecp) (abs)) :use (bvecp-siga) :nonlinearp t)))

(local-defthmd opbgeopa-27
  (implies (and (equal (mulovfl) 0) (> (expa) 0) (< (expa) (expb)))
           (<= (absval (expa) (expt 2 107)) (absval (expb) (expt 2 106))))
  :hints (("Goal" :in-theory (enable absval) :nonlinearp t)))

(local-defthmd opbgeopa-28
  (implies (and (equal (mulovfl) 0) (> (expa) 0) (< (expa) (expb)))
           (<= (absval (expb) (expt 2 106)) (abs (b))))
  :hints (("Goal" :in-theory (e/d (opbgeopa-11 absval bvecp) (abs)) :use (bvecp-sigb-0) :nonlinearp t)))

(local-defthmd opbgeopa-29
  (implies (and (equal (mulovfl) 0) (> (expa) 0) (< (expa) (expb)))
           (< (abs (a)) (abs (b))))
  :hints (("Goal" :use (opbgeopa-28 opbgeopa-26 opbgeopa-27))))

(local-defthmd opbgeopa-30
  (implies (and (equal (mulovfl) 0) (= (expa) 0) (< 0 (expb)))
           (< (siga) (sigb)))
  :hints (("Goal" :use (bvecp-siga-0 bvecp-sigb-0) :in-theory (enable bvecp))))

(local-defthmd opbgeopa-31
  (implies (and (equal (mulovfl) 0) (= (expb) 0) (< 0 (expa)))
           (> (siga) (sigb)))
  :hints (("Goal" :use (bvecp-siga-0 bvecp-sigb-0) :in-theory (enable bvecp))))

(defthmd opbgeopa-b>=a
  (implies (equal (mulovfl) 0)
           (equal (opbgeopa)
                  (if (>= (abs (b)) (abs (a))) 1 0)))
  :hints (("Goal" :use (opbgeopa-12 opbgeopa-19 opbgeopa-24 opbgeopa-29 opbgeopa-30 opbgeopa-31))))

(defthmd expl-rewrite
  (equal (expl) (if (>= (expa) (expb)) (expa) (expb)))
  :hints (("Goal" :in-theory (enable expl) :use (bvecp-expa bvecp-expb))))

(defund exps ()
  (if (>= (expa) (expb)) (expb) (expa)))

(defund explp ()
  (if1 (logand1 (far) (usa)) (1- (expl)) (expl)))

(in-theory (disable (exps) (explp)))

(defthm sigaprime-rewrite
  (equal (sigaprime)
         (if1 (logand1 (far) (usa)) (* 2 (siga)) (siga)))
  :hints (("Goal" :in-theory (enable bvecp sigaprime siga cat)
                  :use (bvecp-fraca))))

(defthm sigbprime-rewrite
  (equal (sigbprime)
         (if1 (logand1 (far) (usa)) (* 2 (sigb)) (sigb)))
  :hints (("Goal" :in-theory (enable bvecp sigbprime sigb cat)
                  :use (bvecp-fracb))))

(defthmd l-rewrite
  (implies (equal (mulovfl) 0)
           (equal (l) (val (signl) (explp) (sigl))))
  :hints (("Goal" :in-theory (enable absval sigbprime-rewrite l bp a far-rewrite
                              bvecp val sigaprime-rewrite opbgeopa expl sigl sigs
                              opblong-rewrite usa-rewrite explp add-lemma signl*)
                  :use (signa-0-1 signb-0-1 opbgeopa-b>=a bvecp-expa bvecp-expb))))

(defund signs ()
  (if1 (opbgeopa)
       (signa)
       (signb)))

(in-theory (disable (signs)))

(defthmd s-rewrite
  (implies (equal (mulovfl) 0)
           (equal (s) (val (signs) (explp) (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :in-theory (enable absval sigbprime-rewrite expdiff a far-rewrite
                              bvecp val sigaprime-rewrite opbgeopa s exps sigl sigs
                              opblong-rewrite usa-rewrite explp add-lemma signs expl bp)
                  :use (signa-0-1 signb-0-1 opbgeopa-b>=a bvecp-expa bvecp-expb))))

(defthmd expdiff-rewrite
  (equal (expdiff)
         (if1 (opbgeopa)
              (if (and (= (expa) 0) (not (= (expb) 0)))
                  (1- (- (expb) (expa)))
                (- (expb) (expa)))
              (if (and (= (expb) 0) (not (= (expa) 0)))
                  (1- (- (expa) (expb)))
                (- (expa) (expb)))))
  :hints (("Goal" :in-theory (enable expdiff bvecp opbgeopa)
                  :use (bvecp-expa bvecp-expb))))

(defthmd rshift-rewrite-1
  (implies (and (= (mulovfl) 0) (< (expdiff) 128))
           (equal (rshift) (expdiff)))
  :hints (("Goal" :in-theory (enable expdiff-rewrite rshift bvecp opbgeopa)
                  :use (bvecp-expa
                        (:instance bits-plus-bits (x (expdiff)) (n 11) (m 0) (p 7))
                        (:instance bits-bounds (x (expdiff)) (i 6) (j 0))))))

(local-defthmd rshift-rewrite-2
  (implies (and (= (mulovfl) 0) (>= (expdiff) 128))
           (>= (rshift) 112))
  :hints (("Goal" :in-theory (enable expdiff-rewrite rshift bvecp opbgeopa)
                  :use (bvecp-expa bvecp-expb
                        (:instance bits-plus-bits (x (expdiff)) (n 11) (m 0) (p 7))
                        (:instance bits-bounds (x (expdiff)) (i 6) (j 0))))))

(defthmd bvecp-sigs
  (bvecp (sigs) 108)
  :hints (("Goal" :in-theory (enable bvecp sigs sigaprime-rewrite sigbprime-rewrite)
                  :use (bvecp-siga bvecp-sigb))))

(defthmd bvecp-sigl
  (bvecp (sigl) 108)
  :hints (("Goal" :in-theory (enable bvecp sigl sigaprime-rewrite sigbprime-rewrite)
                  :use (bvecp-siga bvecp-sigb))))

(defthmd bvecp-sigshft
  (implies (= (mulovfl) 0)
           (bvecp (sigshft) 108))
  :hints (("Goal" :nonlinearp t
                  :use (bvecp-sigs)
                  :in-theory (enable sigshft rshift-rewrite-1 bvecp))))

(local-defthmd sigshft-rewrite-1
  (implies (and (= (mulovfl) 0) (< (expdiff) 128))
           (equal (sigshft) (fl (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :nonlinearp t
                  :use (bvecp-sigs)
                  :in-theory (enable sigshft rshift-rewrite-1 bvecp))))

(local-defthmd sigshft-rewrite-2
  (implies (and (= (mulovfl) 0) (>= (expdiff) 128))
           (equal (fl (* (expt 2 (- (expdiff))) (sigs))) 0))
  :hints (("Goal" :nonlinearp t
                  :use (bvecp-sigs)
                  :in-theory (enable bvecp))))

(local-defthmd sigshft-rewrite-3
  (implies (and (= (mulovfl) 0) (>= (expdiff) 128))
           (equal (sigshft) 0))
  :hints (("Goal" :nonlinearp t
                  :use (rshift-rewrite-2 bvecp-sigs)
                  :in-theory (enable sigshft bvecp))))

(defthmd sigshft-rewrite
  (implies (= (mulovfl) 0)
           (equal (sigshft) (fl (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :nonlinearp t
                  :use (sigshft-rewrite-1 sigshft-rewrite-2 sigshft-rewrite-3))))

(local-defthmd shiftout-rewrite-1
  (implies (and (= (mulovfl) 0) (< (expdiff) 128))
           (equal (shiftout)
                  (if (= (sigshft) (* (expt 2 (- (expdiff))) (sigs))) 0 1)))
  :hints (("Goal" :nonlinearp t
                  :use (bvecp-sigs)
                  :in-theory (enable shiftout sigshft rshift-rewrite-1
                                     bvecp))))

(local-defthmd shiftout-rewrite-2
  (implies (and (= (mulovfl) 0) (>= (expdiff) 128))
           (equal (shiftout)
                  (if (= (sigshft) (* (expt 2 (- (expdiff))) (sigs))) 0 1)))
  :hints (("Goal" :nonlinearp t
                  :use (bvecp-sigs)
                  :in-theory (enable shiftout sigshft-rewrite-3 bvecp))))

(defthmd shiftout-rewrite
  (implies (= (mulovfl) 0)
           (equal (shiftout)
                  (if (= (sigshft) (* (expt 2 (- (expdiff))) (sigs))) 0 1)))
  :hints (("Goal" :use (shiftout-rewrite-1 shiftout-rewrite-2))))

(defthm bitn-siga-0
  (equal (bitn (siga) 0) 0)
  :hints (("Goal" :in-theory (enable siga))))

(defthmd siga-even
  (evenp (siga))
  :hints (("Goal" :use (bvecp-siga
                        (:instance bits-plus-bitn (x (siga)) (n 106) (m 0))))))

(defthmd sigaprime-even
  (evenp (sigaprime))
  :hints (("Goal" :use (siga-even) :in-theory (enable sigaprime-rewrite))))

(defthm bitn-sigb-0
  (equal (bitn (sigb) 0) 0)
  :hints (("Goal" :in-theory (enable sigb))))

(defthmd sigb-even
  (evenp (sigb))
  :hints (("Goal" :use (bvecp-sigb
                        (:instance bits-plus-bitn (x (sigb)) (n 106) (m 0))))))

(defthmd sigbprime-even
  (evenp (sigbprime))
  :hints (("Goal" :use (sigb-even) :in-theory (enable sigbprime-rewrite))))

(defthmd sigs-even
  (evenp (sigs))
  :hints (("Goal" :use (sigaprime-even sigbprime-even) :in-theory (enable sigs))))

(defthm near-shiftout-0-1
  (implies (and (= (mulovfl) 0) (= (far) 0))
           (member (expdiff) '(0 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expdiff-rewrite far-rewrite opbgeopa))))

(defthm near-shiftout-0
  (implies (and (= (mulovfl) 0) (= (far) 0))
           (equal (shiftout) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable shiftout-rewrite sigshft-rewrite)
           :use (sigs-even near-shiftout-0-1))))

(local-defund kk () (mod (sigs) (expt 2 (expdiff))))
(local-in-theory (disable (kk)))

(local-defthmd shiftout-1-bounds-1
  (implies (= (mulovfl) 0)
           (equal (sigs)
                  (+ (* (sigshft) (expt 2 (expdiff)))
                     (kk))))
  :hints (("Goal" :in-theory (enable kk sigshft-rewrite)
                  :use ((:instance mod-def (x (sigs)) (y (expt 2
                                                               (expdiff))))))))

(local-defthmd shiftout-1-bounds-2
  (implies (= (mulovfl) 0)
           (equal (* (expt 2 (- (expdiff))) (sigs))
                  (+ (sigshft)
                     (* (expt 2 (- (expdiff))) (kk)))))
  :hints (("Goal" :use (shiftout-1-bounds-1))))

(local-defthmd shiftout-1-bounds-3
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (not (= (kk) 0)))
  :hints (("Goal" :in-theory (enable shiftout-rewrite shiftout-1-bounds-1))))

(local-defthmd shiftout-1-bounds-4
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (not (= (expdiff) 0)))
  :hints (("Goal" :in-theory (enable shiftout-rewrite sigshft-rewrite))))

(defthmd shiftout-1-bounds-5
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (> (expdiff) 0))
  :hints (("Goal" :use (shiftout-1-bounds-4)
           :in-theory (enable expdiff))))

(local-defthmd shiftout-1-bounds-6
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (evenp (* (sigshft) (expt 2 (expdiff)))))
  :hints (("Goal" :use (shiftout-1-bounds-5))))

(local-defthmd shiftout-1-bounds-7
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (evenp (kk)))
  :hints (("Goal" :use (shiftout-1-bounds-1 shiftout-1-bounds-6 sigs-even))))

(local-defthmd shiftout-1-bounds-8
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (not (evenp (1- (expt 2 (expdiff))))))
  :hints (("Goal" :use (shiftout-1-bounds-5))))

(local-defthm shiftout-1-bounds-9
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (not (= (kk) 1)))
  :rule-classes ()
  :hints (("Goal" :use (shiftout-1-bounds-8))))

(local-defthm shiftout-1-bounds-10
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (not (or (= (kk) 1)
                    (= (kk) (1- (expt 2 (expdiff)))))))
  :rule-classes ()
  :hints (("Goal" :use (shiftout-1-bounds-7 shiftout-1-bounds-9 shiftout-1-bounds-8)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd shiftout-1-bounds-11
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (and (<= 2 (kk))
                (<= (kk) (- (expt 2 (expdiff)) 2))))
  :hints (("Goal" :in-theory (enable kk)
                  :use (shiftout-1-bounds-3 shiftout-1-bounds-10
                        (:instance natp-mod (m (sigs)) (n (expt 2 (expdiff))))
                        (:instance mod-bnd-1 (m (sigs)) (n (expt 2 (expdiff))))))))

(local-defthmd shiftout-1-bounds-12
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (and (<= (expt 2 (- 1 (expdiff)))
                    (* (expt 2 (- (expdiff))) (kk)))
                (<= (* (expt 2 (- (expdiff))) (kk))
                    (- 1 (expt 2 (- 1 (expdiff)))))))
  :hints (("Goal" :nonlinearp t
           :use (shiftout-1-bounds-11))))

(defthmd shiftout-1-bounds
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (and (<= (+ (sigshft) (expt 2 (- 1 (expdiff))))
                    (* (expt 2 (- (expdiff))) (sigs)))
                (<= (* (expt 2 (- (expdiff))) (sigs))
                    (- (1+ (sigshft)) (expt 2 (- 1 (expdiff)))))))
  :hints (("Goal" :use (shiftout-1-bounds-2 shiftout-1-bounds-12))))


