(in-package "RTL")

(include-book "alignment")

(local-defthmd sum-lsa-1
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (< (sigl) (expt 2 107)))
  :hints (("Goal" :in-theory (enable bvecp sigl sigaprime sigbprime)
                  :use (bvecp-siga bvecp-sigb))))

(local-defthmd sum-lsa-2
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (< (sigs) (expt 2 107)))
  :hints (("Goal" :in-theory (enable bvecp sigs sigaprime sigbprime)
           :use (bvecp-siga bvecp-sigb))))

(local-defthmd sum-lsa-3
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (< (sigshft) (expt 2 107)))
  :hints (("Goal" :in-theory (enable sigshft-rewrite)
                  :nonlinearp t
                  :use (sum-lsa-2))))

(local-defthmd sum-lsa-4
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (equal (sum) (+ (sigl) (sigshft))))
  :hints (("Goal" :in-theory (enable add-lemma sum* bvecp)
           :use (sum-lsa-1 sum-lsa-3))))

(local-defthmd sum-lsa-5
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (equal (abs (+ (a) (bp))) (+ (abs (a)) (abs (bp)))))
  :hints (("Goal" :in-theory (enable usa-rewrite a bp val absval))))

(local-defthmd sum-lsa-6
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (equal (abs (+ (a) (bp))) (+ (abs (l)) (abs (s)))))
  :hints (("Goal" :use sum-lsa-5 :in-theory (enable l s))))

(local-defthmd sum-lsa-7
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (equal (abs (+ (a) (bp)))
                  (absval (explp) (+ (sigl) (* (expt 2 (- (expdiff))) (sigs))))))
  :hints (("Goal" :in-theory (enable val absval l-rewrite s-rewrite)
                  :use (sum-lsa-6))))

(local-defthmd sum-lsa-8
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 0))
           (= (sum) (+ (sigl) (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :in-theory (enable sum-lsa-4 shiftout-rewrite
                                     sigshft-rewrite))))

(local-defthmd sum-lsa-9
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 0))
           (equal (abs (+ (a) (bp)))
                  (absval (explp) (sum))))
  :hints (("Goal" :use (sum-lsa-7 sum-lsa-8))))

(local-defthm signa-sign
  (or (= (a) 0)
      (iff (> (a) 0) (= (signa) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable a val absval))))

(local-defthm signb-sign
  (or (= (bp) 0)
      (iff (> (bp) 0) (= (signb) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bp val absval))))

(local-defthmd chop-sigb-1
  (implies (= (bits (sigb) 52 0) 0)
           (integerp (* (expt 2 -53) (sigb))))
  :hints (("Goal" :in-theory (enable bits)
                  :use ((:instance mod-def (x (sigb)) (y (expt 2 53)))))))

(local-defthmd chop-sigb
  (implies (= (bits (sigb) 52 0) 0)
           (equal (chop (sigb) -53) (sigb)))
  :hints (("Goal" :use (chop-sigb-1) :in-theory (enable chop))))


(local-defthm sum-lsa-10
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (equal (b) (bp)))
  :hints (("Goal" :in-theory (enable chop-sigb bp val)
           :use (signa-sign signb-sign signa-0-1 signb-0-1 expb-pos-b expb-0-b))))

(local-defthmd sum-lsa-11
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 0) (= (shiftout) 0))
           (and (= (stk) 0)
	        (equal (abs (+ (a) (b)))
	               (absval (explp) (sum)))))
  :hints (("Goal" :in-theory (e/d (stk* add-lemma))
           :use (sum-lsa-9 expb-pos-b expb-0-b))))

(local-defthm stk-lsa-2
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 1))
           (equal (stk) 1))
  :hints (("Goal" :use near-shiftout-0 :in-theory (enable add-lemma stk*))))

(local-defthmd sum-lsa-17
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 1))
           (< (sum) (+ (sigl) (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :in-theory (enable sum-lsa-4 shiftout-rewrite sigshft-rewrite))))

(local-defthmd sum-lsa-18
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 1))
           (<= (+ (sigl) (* (expt 2 (- (expdiff))) (sigs)))
               (- (1+ (sum)) (expt 2 (- 1 (expdiff))))))
  :hints (("Goal" :in-theory (enable sum-lsa-4)
           :use (shiftout-1-bounds-5 shiftout-1-bounds))))

(local-defthm absval-monotone
  (implies (and (integerp e) (rationalp s1) (rationalp s2) (< s1 s2))
           (< (absval e s1) (absval e s2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable absval))))

(defthm integerp-sum
  (integerp (sum))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable sum* add-lemma))))

(local-defthmd sum-lsa-19
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 1))
           (< (absval (explp) (sum))
              (abs (+ (a) (bp)))))
  :hints (("Goal" :use (sum-lsa-17 sum-lsa-7
                        (:instance absval-monotone (e (explp)) (s1 (sum))
                                                   (s2 (+ (sigl) (* (expt 2 (- (expdiff))) (sigs))))))
                  :in-theory (disable abs))))

(local-defthm absval-weakly-monotone
  (implies (and (integerp e) (rationalp s1) (rationalp s2) (<= s1 s2))
           (<= (absval e s1) (absval e s2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable absval))))

(local-defthmd sum-lsa-20
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 1))
           (<= (abs (+ (a) (bp)))
               (absval (explp) (- (1+ (sum)) (expt 2 (- 1 (expdiff)))))))
  :hints (("Goal" :use (sum-lsa-18 sum-lsa-7
                        (:instance absval-weakly-monotone
			           (e (explp))
	                           (s1 (+ (sigl) (* (expt 2 (- (expdiff))) (sigs))))
				   (s2 (- (1+ (sum)) (expt 2 (- 1 (expdiff)))))))
                  :in-theory (disable abs))))

(local-defthmd sum-lsa-21
  (implies (and (= (mulovfl) 0) (= (usa) 0) (= (shiftout) 1))
           (< (abs (+ (a) (bp)))
              (absval (explp) (1+ (sum)))))
  :hints (("Goal" :use (sum-lsa-20
                        (:instance absval-monotone
			           (e (explp))
	                           (s1 (- (1+ (sum)) (expt 2 (- 1 (expdiff)))))
				   (s2 (1+ (sum)))))
                  :in-theory (disable abs))))

(local-defthm sum-lsa-22
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 0) (= (shiftout) 1) (= (mulstk) 0))
           (and (< (absval (explp) (sum))
	           (abs (+ (a) (b))))
                (< (abs (+ (a) (b)))
                   (absval (explp) (1+ (sum))))))
  :rule-classes ()
  :hints (("Goal" :use (sum-lsa-21 sum-lsa-19)
                  :in-theory (e/d (expb-pos-b bp) (abs)))))

(local-defthmd sum-lsa
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 0))
           (and (<= (absval (explp) (sum))
                    (abs (+ (a) (b))))
                (< (abs (+ (a) (b)))
                   (absval (explp) (1+ (sum))))))
  :hints (("Goal" :use (sum-lsa-11 sum-lsa-22
                        (:instance absval-monotone (e (explp)) (s1 (sum)) (s2 (1+ (sum))))))))

(local-defthmd stk-lsa
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 0))
           (iff (= (absval (explp) (sum))
                   (abs (+ (a) (b))))
                (= (stk) 0)))
  :hints (("Goal" :use (sum-lsa-22 sum-lsa-11)))) 
  
(local-defthm absval-sub
  (implies (and (integerp e) (rationalp s1) (rationalp s2))
           (equal (absval e (- s1 s2))
	          (- (absval e s1) (absval e s2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable absval))))

(local-defthmd sum-usa-1
  (implies (and (= (mulovfl) 0) (= (b) (bp)) (= (usa) 1))
           (equal (abs (+ (a) (b))) (- (abs (l)) (abs (s)))))
  :hints (("Goal" :use (signa-sign signb-sign signa-0-1 signb-0-1) :in-theory (enable usa-rewrite l s))))

(local-defthmd sum-usa-2
  (implies (= (mulovfl) 0)
           (equal (abs (l)) (absval (explp) (sigl))))
  :hints (("Goal" :in-theory (enable l-rewrite val absval))))

(local-defthmd sum-usa-3
  (implies (= (mulovfl) 0)
           (equal (abs (s)) (absval (explp) (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :in-theory (enable s-rewrite val absval))))

(local-defthmd sum-usa-4
  (implies (and (= (mulovfl) 0) (= (b) (bp)) (= (usa) 1))
           (equal (abs (+ (a) (bp)))
                  (absval (explp) (- (sigl) (* (expt 2 (- (expdiff))) (sigs))))))
  :hints (("Goal" :in-theory (e/d (sum-usa-1 sum-usa-2 sum-usa-3) (abs))
                  :use ((:instance absval-sub (e (explp)) (s1 (sigl)) (s2 (* (expt 2 (- (expdiff))) (sigs))))))))

(local-defthm sum-usa-5
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 1))
           (equal (far) 1))
  :hints (("Goal" :use (near-shiftout-0) :in-theory (enable far-rewrite))))

(local-defthm sum-usa-6
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 1))
           (equal (stk) 1))
  :hints (("Goal" :in-theory (enable add-lemma stk*))))

(local-defthmd sum-usa-7
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 1))
           (equal (sum) (bits (+ (sigl) (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-usa-8
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 1))
           (equal (sum) (bits (- (sigl) (1+ (sigshft))) 107 0)))
  :hints (("Goal" :in-theory (enable sum-usa-7 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (1+ (sigshft)))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthmd sum-usa-9
  (implies (and (= (mulovfl) 0) (= (expdiff) 0))
           (<= (* (expt 2 (- (expdiff))) (sigs)) (sigl)))
  :hints (("Goal" :in-theory (enable cat siga sigb expdiff sigs sigl opbgeopa bvecp)
                  :use (bvecp-siga bvecp-sigb bvecp-siga-0 bvecp-sigb-0 bvecp-expa bvecp-expb))))

(local-defthmd sum-usa-10
  (implies (and (= (mulovfl) 0) (> (expdiff) 0))
           (< (sigs) (* 2 (sigl))))
  :Hints (("Goal" :in-theory (enable cat siga sigb expdiff sigs sigl opbgeopa bvecp)
                  :use (bvecp-siga bvecp-sigb bvecp-siga-0 bvecp-sigb-0 bvecp-expa bvecp-expb))))

(local-defthmd sum-usa-11
  (implies (and (= (mulovfl) 0) (> (expdiff) 0))
           (<= (* (expt 2 (- (expdiff))) (sigs)) (sigl)))
  :hints (("Goal" :use (sum-usa-10) :nonlinearp t)))

(local-defthmd sum-usa-12
  (implies (= (mulovfl) 0)
           (<= (* (expt 2 (- (expdiff))) (sigs)) (sigl)))
  :hints (("Goal" :use (sum-usa-11 sum-usa-9))))

(local-defthmd sum-usa-13
  (implies (= (mulovfl) 0)
           (<= (sigshft) (sigl)))
  :hints (("Goal" :use (sum-usa-12) :in-theory (enable sigshft-rewrite))))

(local-defthmd sum-usa-14
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (< (sigshft) (sigl)))
  :hints (("Goal" :use (sum-usa-12) :in-theory (enable sigshft-rewrite shiftout-rewrite))))

(local-defthmd sum-usa-15
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 1))
           (equal (sum) (- (sigl) (1+ (sigshft)))))
  :hints (("Goal" :in-theory (enable sum-usa-8 bvecp)
                  :use (bvecp-sigl sum-usa-14))))

(local-defthm sum-usa-16
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 1))
           (and (<= (+ (sum) (expt 2 (- 1 (expdiff))))
	            (- (sigl) (* (expt 2 (- (expdiff))) (sigs))))
		(<= (- (sigl) (* (expt 2 (- (expdiff))) (sigs)))
		    (- (1+ (sum)) (expt 2 (- 1 (expdiff)))))))
  :rule-classes ()
  :hints (("Goal" :use (shiftout-1-bounds) :in-theory (enable sum-usa-15))))

(local-defthm rat-abs
  (implies (rationalp x) (rationalp (abs x)))
  :rule-classes (:type-prescription :rewrite))

(local-defthm sum-usa-17
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (b) (bp)) (= (shiftout) 1))
           (and (<= (+ (absval (explp) (sum)) (absval (explp) (expt 2 (- 1 (expdiff)))))
	            (abs (+ (a) (bp))))
		(<= (abs (+ (a) (bp)))
		    (- (absval (explp) (1+ (sum))) (absval (explp) (expt 2 (- 1 (expdiff))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (absval) (abs))
                  :use (sum-usa-16 sum-usa-4)
		  :nonlinearp t)))

(local-defthm sum-usa-18
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 1) (= (shiftout) 1))
           (and (< (absval (explp) (sum))
                   (abs (+ (a) (b))))
		(< (abs (+ (a) (b)))
                   (absval (explp) (1+ (sum))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable absval)
                  :use (expb-pos-b bp sum-usa-17))))

(local-defthm sum-usa-23
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))) (= (shiftout) 0))
           (equal (stk) 0))
  :hints (("Goal" :use (expb-pos-b)
                  :in-theory (enable add-lemma stk*))))

(local-defthm sum-usa-24
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (bits (+ (sigl) 1 (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-usa-25
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (bits (- (sigl) (sigshft)) 107 0)))
  :hints (("Goal" :in-theory (enable sum-usa-24 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (sigshft))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthmd sum-usa-26
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (- (sigl) (sigshft))))
  :hints (("Goal" :in-theory (enable sum-usa-25 bvecp)
                  :use (bvecp-sigl sum-usa-13))))

(defthmd sum-usa-27
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (- (sigl) (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :in-theory (enable sum-usa-26 sigshft-rewrite shiftout-rewrite))))

(local-defthmd sum-usa-28
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 1) (= (shiftout) 0))
           (equal (abs (+ (a) (b)))
                  (absval (explp) (sum))))
  :hints (("Goal" :in-theory (e/d (expb-pos-b sum-usa-4 sum-usa-27) (abs)))))

(local-defthmd sum-usa-29
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 1) (= (shiftout) 0))
           (and (<=  (absval (explp) (sum)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (explp) (1+ (sum))))
		(iff (= (absval (explp) (sum)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :hints (("Goal" :use sum-usa-28 :in-theory (e/d (absval) (abs)))))

(local-defthmd sum-usa
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))) (= (usa) 1))
           (and (<=  (absval (explp) (sum)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (explp) (1+ (sum))))
		(iff (= (absval (explp) (sum)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :hints (("Goal" :use (sum-usa-18 sum-usa-29)
                  :in-theory (enable add-lemma stk*))))

(defthm sum-bounds-0
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (explp) (sum)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (explp) (1+ (sum))))
		(iff (= (absval (explp) (sum)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ()
  :hints (("Goal" :use (sum-lsa stk-lsa sum-usa))))



(local-defthm sum-1-1
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1))
	   (equal (expa) 0))
  :hints (("Goal" :in-theory (enable opbgeopa))))

(local-defthm sum-1-2
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1))
           (and (equal (expl) 0)
	        (equal (explp) 0)))
  :hints (("Goal" :in-theory (enable expl-rewrite explp far-rewrite))))

(local-defthm sum-1-3
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1))
           (and (equal (sigl) (sigb))
		(equal (sigs) (siga))))
  :hints (("Goal" :in-theory (enable sigl sigs far-rewrite))))

(local-defthm sum-1-4
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1))
	   (equal (shiftout) 0))
  :hints (("Goal" :in-theory (enable expdiff-rewrite sigshft-rewrite shiftout-rewrite))))

(local-defthmd sum-1-5
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
	   (equal (sum) (+ (siga) (sigb))))
  :hints (("Goal" :in-theory (enable sigshft-rewrite expdiff-rewrite sum-lsa-4))))

(local-defthmd sum-1-6
  (implies (and (rationalp a) (rationalp b) (integerp k) (integerp (* (expt 2 k) a)))
           (equal (chop (+ a b) k)
	          (+ a (chop b k))))
  :hints (("Goal" :in-theory (e/d (chop) (fl+int-rewrite))
                  :use ((:instance fl+int-rewrite (x (* (expt 2 k) b)) (n (* (expt 2 k) a)))))))

(local-defthmd sum-1-7
  (equal (bits (fraca) 52 0) 0)
  :hints (("Goal" :in-theory (enable fraca frac opax checkdenorm opaz))))

(local-defthmd sum-1-8
  (equal (bits (siga) 53 0) 0)
  :hints (("Goal" :in-theory (enable sum-1-7 siga))))

(local-defthmd sum-1-9
  (integerp (* (expt 2 -53) (siga)))
  :hints (("Goal" :in-theory (enable bits)
                  :use (sum-1-8 (:instance mod-def (x (siga)) (y (expt 2 54)))))))

(local-defthmd sum-1-10
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
           (equal (chop (sum) -53)
                  (+ (siga) (chop (sigb) -53))))
  :hints (("Goal" :use (sum-1-9 (:instance sum-1-6 (a (siga)) (b (sigb)) (k -53)))
                  :in-theory (enable sum-1-5))))

(local-defthmd sum-1-11
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
           (equal (absval (explp) (chop (sum) -53))
                  (+ (absval (explp) (siga)) (absval (explp) (chop (sigb) -53)))))
  :hints (("Goal" :in-theory (enable sum-1-10 absval))))

(defthmd absval-a>=0
  (>= (absval (expa) (siga)) 0)
  :hints (("Goal" :in-theory (enable absval))))

(defthmd absval-b>=0
  (>= (absval (expb) (sigb)) 0)
  :hints (("Goal" :in-theory (enable absval))))

(local-defthmd sum-1-12
  (equal (abs (a)) (absval (expa) (siga)))
  :hints (("Goal" :in-theory (enable a val) :use (absval-a>=0))))

(local-defthmd sum-1-13
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
           (< (absval (explp) (chop (sum) -53))
              (+ (abs (a)) (abs (b)))))
  :hints (("Goal" :in-theory (enable sum-1-12)
                  :use (sum-1-11 expb-0-b))))

(local-defthmd sum-1-14
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
           (equal (absval (explp) (+ (expt 2 53) (chop (sum) -53)))
                  (+ (absval (explp) (siga)) (absval (explp) (+ (expt 2 53) (chop (sigb) -53))))))
  :hints (("Goal" :in-theory (enable absval) :use (sum-1-10))))

(local-defthmd sum-1-15
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
           (> (absval (explp) (+ (expt 2 53) (chop (sum) -53)))
              (+ (abs (a)) (abs (b)))))
  :hints (("Goal" :in-theory (enable sum-1-12)
                  :use (sum-1-14 expb-0-b))))

(local-defthmd sum-1-16
  (implies (and (= (mulovfl) 0) (= (usa) 0))
           (equal (abs (+ (a) (b))) (+ (abs (a)) (abs (b)))))
  :hints (("Goal" :use (signa-0-1 signb-0-1 signa-sign signb-sign expb-0-b expb-pos-b)
                  :in-theory (enable usa-rewrite))))

(local-defthmd sum-1-17
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
		(< (abs (+ (a) (b)))
		   (absval (explp) (+ (expt 2 53) (chop (sum) -53))))))
  :hints (("Goal" :use (sum-1-15 sum-1-16 sum-1-13))))

(local-defthmd sum-1-18
  (implies (and (= (mulovfl) 0) (= (opbgeopa) 1) (= (usa) 1))
	   (equal (abs (+ (a) (b)))
	          (- (abs (b)) (abs (a)))))
  :hints (("Goal" :in-theory (enable bp usa-rewrite a val absval opbgeopa-b>=a)
                  :nonlinearp t
                  :use (signa-0-1 signb-0-1 absval-a>=0 absval-b>=0 expb-0-b expb-pos-b))))

(local-defthmd sum-1-19
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 1) (= (opbgeopa) 1))
           (equal (sum) (bits (+ (sigl) 1 (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-1-20
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 1) (= (opbgeopa) 1))
           (equal (sum) (bits (- (sigl) (sigshft)) 107 0)))
  :hints (("Goal" :in-theory (enable sum-1-19 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (sigshft))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthmd sum-1-21
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (usa) 1) (= (opbgeopa) 1))
           (equal (sum) (- (sigb) (siga))))
  :hints (("Goal" :in-theory (enable sigshft-rewrite expdiff-rewrite sum-1-20 bvecp)
                  :use (bvecp-sigl sum-usa-13))))

(local-defthmd sum-1-22
  (implies (and (rationalp a) (rationalp b) (integerp k) (integerp (* (expt 2 k) a)))
           (equal (chop (- b a) k)
	          (- (chop b k) a)))
  :hints (("Goal" :in-theory (e/d (chop) (fl+int-rewrite))
                  :use ((:instance fl+int-rewrite (x (* (expt 2 k) b)) (n (- (* (expt 2 k) a))))))))

(local-defthmd sum-1-23
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1))
           (equal (chop (sum) -53)
                  (- (chop (sigb) -53) (siga))))
  :hints (("Goal" :use (sum-1-9 (:instance sum-1-22 (a (siga)) (b (sigb)) (k -53)))
                  :in-theory (enable sum-1-21))))

(local-defthmd sum-1-24
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1))
           (equal (absval (explp) (chop (sum) -53))
                  (- (absval (explp) (chop (sigb) -53)) (absval (explp) (siga)))))
  :hints (("Goal" :in-theory (enable sum-1-23 absval))))

(local-defthmd sum-1-25
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1))
           (< (absval (explp) (chop (sum) -53))
              (- (abs (b)) (abs (a)))))
  :hints (("Goal" :in-theory (enable sum-1-12)
                  :use (sum-1-24 expb-0-b))))

(local-defthmd sum-1-26
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1))
           (equal (absval (explp) (+ (expt 2 53) (chop (sum) -53)))
                  (- (absval (explp) (+ (expt 2 53) (chop (sigb) -53))) (absval (explp) (siga)))))
  :hints (("Goal" :in-theory (enable absval) :use (sum-1-23))))

(local-defthmd sum-1-27
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1))
           (> (absval (explp) (+ (expt 2 53) (chop (sum) -53)))
              (- (abs (b)) (abs (a)))))
  :hints (("Goal" :in-theory (enable sum-1-12)
                  :use (sum-1-26 expb-0-b))))

(local-defthmd sum-1-28
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
		(< (abs (+ (a) (b)))
		   (absval (explp) (+ (expt 2 53) (chop (sum) -53))))))
  :hints (("Goal" :use (sum-1-25 sum-1-18 sum-1-27))))

(local-defthmd sum-1-b
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
		(< (abs (+ (a) (b)))
		   (absval (explp) (+ (expt 2 53) (chop (sum) -53))))))
  :hints (("Goal" :use (sum-1-28 sum-1-17))))

(local-defthm sum-a-1
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0))
           (and (equal (sigl) (sigaprime))
		(equal (sigs) (sigbprime))))
  :hints (("Goal" :in-theory (enable sigl sigs far-rewrite))))

(local-defthmd sum-a-2
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0))
           (equal (sigshft) (fl (* (expt 2 (- (expdiff))) (sigs))))) 
  :hints (("Goal" :in-theory (enable sigshft-rewrite))))

(local-defthm sum-a-3
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (and (equal (sigl) (siga))
	        (equal (sigs) (sigb))))
  :hints (("Goal" :in-theory (enable sigaprime-rewrite sigbprime-rewrite))))

(local-defthm sum-a-4
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (equal (explp) (expa)))
  :hints (("Goal" :in-theory (enable expl-rewrite explp opbgeopa))))

(local-defthmd sum-a-5
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (equal (sum) (+ (siga) (fl (* (expt 2 (- (expdiff))) (sigb))))))
  :hints (("Goal" :in-theory (enable sum-lsa-4 sum-a-2))))

(local-defthmd sum-a-6
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (<= (chop (fl (* (expt 2 (- (expdiff))) (sigb))) -53)
	       (* (expt 2 (- (expdiff))) (chop (sigb) -53))))
  :hints (("Goal" :use ((:instance chop-int-bounds (n (expdiff)) (k 53) (x (sigb)))))))

(local-defthmd sum-a-7
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (equal (absval (explp) (chop (sum) -53))
	          (+ (absval (expa) (siga))
		     (absval (expa) (chop (fl (* (expt 2 (- (expdiff))) (sigb))) -53)))))
  :hints (("Goal" :use (sum-1-9 (:instance sum-1-6 (a (siga)) (b (fl (* (expt 2 (- (expdiff))) (sigb)))) (k -53)))
                  :in-theory (enable absval sum-a-5))))

(local-defthmd sum-a-8
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (<= (absval (expa) (chop (fl (* (expt 2 (- (expdiff))) (sigb))) -53))
	       (absval (expa) (* (expt 2 (- (expdiff))) (chop (sigb) -53)))))
  :hints (("Goal" :use (sum-a-6) :in-theory (enable absval) :nonlinearp t)))

(local-defthmd sum-a-9
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (= (absval (expa) (* (expt 2 (- (expdiff))) (chop (sigb) -53)))
	      (absval 0 (chop (sigb) -53))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite absval))))

(local-defthmd sum-a-10
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (< (absval (explp) (chop (sum) -53))
	      (+ (abs (a)) (abs (b)))))
  :hints (("Goal" :use (sum-a-7 sum-a-8 sum-a-9 expb-0-b) :in-theory (e/d (sum-1-12) (abs)))))

(local-defthmd sum-a-11
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (<= (* (expt 2 (- (expdiff))) (+ (expt 2 53) (chop (sigb) -53)))
	       (+ (chop (fl (* (expt 2 (- (expdiff))) (sigb))) -53)
	          (expt 2 53))))
  :hints (("Goal" :use ((:instance chop-int-bounds (n (expdiff)) (k 53) (x (sigb)))))))

(local-defthmd sum-a-12
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (equal (absval (explp) (+ (chop (sum) -53) (expt 2 53)))
	          (+ (absval (expa) (siga))
		     (absval (expa) (+ (chop (fl (* (expt 2 (- (expdiff))) (sigb))) -53) (expt 2 53))))))
  :hints (("Goal" :use (sum-1-9
                        (:instance sum-1-6 (a (siga)) (b (fl (* (expt 2 (- (expdiff))) (sigb)))) (k -53)))
                  :in-theory (enable absval sum-a-5))))

(local-defthmd sum-a-13
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (>= (absval (expa) (+ (chop (fl (* (expt 2 (- (expdiff))) (sigb))) -53) (expt 2 53)))
	       (absval (expa) (* (expt 2 (- (expdiff))) (+ (chop (sigb) -53) (expt 2 53))))))
  :hints (("Goal" :use (sum-a-11) :in-theory (enable absval) :nonlinearp t)))

(local-defthmd sum-a-14
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (= (absval (expa) (* (expt 2 (- (expdiff))) (+ (chop (sigb) -53) (expt 2 53))))
	      (absval 0 (+ (chop (sigb) -53) (expt 2 53)))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite absval))))

(local-defthmd sum-a-15
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (> (absval (explp) (+ (expt 2 53) (chop (sum) -53)))
	      (+ (abs (a)) (abs (b)))))
  :hints (("Goal" :use (sum-a-12 sum-a-13 sum-a-14 expb-0-b) :in-theory (e/d (sum-1-12) (abs)))))

(local-defthmd sum-1-a-lsa
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
		(< (abs (+ (a) (b)))
		   (absval (explp) (+ (expt 2 53) (chop (sum) -53))))))
  :hints (("Goal" :use (sum-a-15 sum-a-10 sum-1-16))))




(local-defund x0 () (* (expt 2 (+ 104 (expt 2 10))) (abs (b))))

(local-defthm rat-x0
  (rationalp (x0))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable x0))))

(local-defthmd sum-a-16
  (equal (absval 0 (x0)) (abs (b)))
  :hints (("Goal" :in-theory (e/d (absval x0) (abs)))))

(local-defund n ()
  (if (> (expa) 1) (- (expa) 2) 0))

(local-in-theory (disable (x0) (n)))

(local-defthmd sum-a-17
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
	   (equal (* (expt 2 (- (expdiff))) (sigbprime))
	          (* (expt 2 (- (n))) (sigb))))
  :hints (("Goal" :in-theory (enable n far-rewrite expdiff-rewrite opbgeopa sigbprime-rewrite))))

(local-defthmd sum-a-18
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
	   (equal (absval (explp) (* (expt 2 (- (n))) (x0)))
	          (absval 0 (x0))))
  :hints (("Goal" :in-theory (enable absval n far-rewrite expdiff-rewrite opbgeopa explp expl-rewrite))))

(local-defthmd sum-a-19
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
	   (and (< (absval 0 (chop (sigb) -53)) (absval 0 (x0)))
	        (< (absval 0 (x0)) (absval 0 (+ (chop (sigb) -53) (expt 2 53))))))
  :hints (("Goal" :in-theory (enable sum-a-16)
                  :use (expb-0-b))))

(local-defthmd sum-a-20
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
	   (and (< (chop (sigb) -53) (x0))
	        (< (x0) (+ (chop (sigb) -53) (expt 2 53)))))
  :hints (("Goal" :in-theory (enable absval)
                  :use (sum-a-19)
		  :nonlinearp t)))

(local-defthmd sum-a-21
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (Opbgeopa) 0) (= (usa) 1))
	   (and (< (fl (/ (sigb) (expt 2 53))) (/ (x0) (expt 2 53)))
	        (< (/ (x0) (expt 2 53)) (1+ (fl (/ (sigb) (expt 2 53)))))))
  :hints (("Goal" :in-theory (enable chop)
                  :use (sum-a-20)
		  :nonlinearp t)))

(local-defthmd sum-a-22
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
	   (and (not (integerp (/ (x0) (expt 2 53))))
	        (= (fl (/ (x0) (expt 2 53)))
		   (fl (/ (sigb) (expt 2 53))))))
  :hints (("Goal" :use (sum-a-21))))

(local-defthmd sum-a-cin-1
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (not (integerp (/ (sigb) (expt 2 53)))))
  :hints (("Goal" :in-theory (enable bits)
                  :use ((:instance mod-def (x (sigb)) (y (expt 2 53)))))))

(local-defthm natp-n
  (natp (n))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable n))))

(local-defthmd sum-a-cin-2
  (implies (and (integerp x) (natp n))
           (integerp (* x (expt 2 n)))))

(local-defthmd sum-a-cin-3
  (implies (and (rationalp x) (integerp k) (natp n) (integerp (/ x (expt 2 (+ k n)))))
           (integerp (/ x (expt 2 k))))
  :hints (("Goal" :use ((:instance sum-a-cin-2 (x (/ x (expt 2 (+ k n)))))))))

(local-defthmd sum-a-cin-4
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (not (integerp (/ (x0) (expt 2 (+ (n) 53))))))
  :hints (("Goal" :use (sum-a-22 (:instance sum-a-cin-3 (k 53) (n (n)) (x (x0)))))))

(local-defthmd sum-a-cin-5
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (not (integerp (/ (sigb) (expt 2 (+ (n) 53))))))
  :hints (("Goal" :use (sum-a-cin-1 (:instance sum-a-cin-3 (k 53) (n (n)) (x (sigb)))))))
  
(local-defthmd sum-a-cin-6
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (fl (- (/ (sigb) (expt 2 (+ (n) 53)))))
	          (fl (- (/ (x0) (expt 2 (+ (n) 53)))))))
  :hints (("Goal" :use (sum-a-cin-1 sum-a-22 sum-a-cin-4 sum-a-cin-5
                        (:instance fl/int-rewrite (x (/ (sigb) (expt 2 53))) (n (expt 2 (n))))
                        (:instance fl/int-rewrite (x (/ (x0) (expt 2 53))) (n (expt 2 (n))))
			(:instance minus-fl (x (/ (x0) (expt 2 (+ (n) 53)))))
			(:instance minus-fl (x (/ (sigb) (expt 2 (+ (n) 53)))))))))

(local-defthmd sum-a-cin-7
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (chop (- (/ (sigb) (expt 2 (n)))) -53)
	          (chop (- (/ (x0) (expt 2 (n)))) -53)))
  :hints (("Goal" :use (sum-a-cin-6) :in-theory (enable chop))))

(local-defthmd sum-a-cin-8
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (bits (+ (sigl) 1 (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-a-cin-9
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (bits (- (sigl) (sigshft)) 107 0)))
  :hints (("Goal" :in-theory (enable sum-a-cin-8 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (sigshft))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthmd sum-a-cin-10
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (- (sigl) (sigshft))))
  :hints (("Goal" :in-theory (enable sum-a-cin-9 bvecp)
                  :use (sum-usa-13 bvecp-sigl))))

(local-defthmd sum-a-cin-11
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (sum) (- (sigaprime) (* (expt 2 (- (n))) (sigb)))))
  :hints (("Goal" :use (sum-a-17) :in-theory (enable shiftout-rewrite sum-a-cin-10 sum-a-2))))

(local-defthmd sum-a-34
  (integerp (* (expt 2 -53) (sigaprime)))
  :hints (("Goal" :use (sum-1-9)
                  :in-theory (enable sigaprime-rewrite))))

(local-defthmd sum-a-cin-12
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 0))
           (equal (chop (sum) -53)
                  (chop (- (sigaprime) (* (expt 2 (- (n))) (x0))) -53)))
  :hints (("Goal" :use (sum-a-cin-7 sum-a-34
                        (:instance sum-1-6 (a (sigaprime)) (b (- (* (expt 2 (- (n))) (sigb)))) (k -53))
                        (:instance sum-1-6 (a (sigaprime)) (b (- (* (expt 2 (- (n))) (x0)))) (k -53)))
                  :in-theory (enable sum-a-cin-11))))

(local-defthmd sum-a-27
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (sum) (bits (+ (sigl) (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-a-28
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (sum) (bits (- (sigl) (1+ (sigshft))) 107 0)))
  :hints (("Goal" :in-theory (enable sum-a-27 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (1+ (sigshft)))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthm sum-a-29
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (< (sigb) (siga)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat opbgeopa sigb siga bvecp)
                  :use (bvecp-fraca bvecp-fracb))))

(local-defthm sum-a-30
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (< (sigs) (sigl)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigs sigl sigaprime-rewrite sigbprime-rewrite)
           :use (sum-a-29))))

(local-defthm sum-a-31
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (< (sigshft) (sigl)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigshft-rewrite)
                  :nonlinearp t
                  :use (sum-a-30))))

(local-defthm sum-a-32
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (sum) (- (sigl) (1+ (sigshft)))))
  :hints (("Goal" :in-theory (enable sum-a-28 bvecp)
                  :use (sum-a-31 bvecp-sigl))))

(local-defthm sum-a-33
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (sum) (- (sigaprime) (1+ (fl (* (expt 2 (- (n))) (sigb)))))))
  :hints (("Goal" :in-theory (enable sum-a-32 sigshft-rewrite)
                  :use (sum-a-17))))

(local-defthmd sum-a-35
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (chop (sum) -53)
	          (+ (sigaprime) (chop (- (1+ (fl (* (expt 2 (- (n))) (sigb))))) -53))))
  :hints (("Goal" :in-theory (enable sum-a-33)
                  :use (sum-a-34 (:instance sum-1-6 (k -53) (a (sigaprime)) (b (- (1+ (fl (* (expt 2 (- (n))) (sigb)))))))))))

(local-defthmd sum-a-36
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (chop (- (1+ (fl (* (expt 2 (- (n))) (sigb))))) -53)
	          (chop (- (* (expt 2 (- (n))) (x0))) -53)))
  :hints (("Goal" :use (sum-a-22 (:instance chop-int-neg (x (x0)) (n (n)) (k 53) (y (sigb)))))))

(local-defthmd sum-a-37-a
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (chop (sum) -53)
	          (+ (sigaprime) (chop (- (* (expt 2 (- (n))) (x0))) -53))))
  :hints (("Goal" :use (sum-a-35 sum-a-36))))

(local-defthmd sum-a-37
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (and (= (shiftout) 0) (= (mulstk) 0))))
           (equal (chop (sum) -53)
	          (chop (- (sigaprime) (* (expt 2 (- (n))) (x0))) -53)))
  :hints (("Goal" :use (sum-a-34 sum-a-37-a
                        (:instance sum-1-6 (k -53) (a (sigaprime)) (b (- (* (expt 2 (- (n))) (x0)))))))))

 (local-defthmd sum-a-38
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (equal (chop (sum) -53)
	          (chop (- (sigaprime) (* (expt 2 (- (n))) (x0))) -53)))
  :hints (("Goal" :use (sum-a-37 sum-a-cin-12) :in-theory (theory 'minimal-theory))))

(local-defthmd sum-a-39
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (and (<= (chop (sum) -53)
	            (- (sigaprime) (* (expt 2 (- (n))) (x0))))
	        (< (- (sigaprime) (* (expt 2 (- (n))) (x0)))
		   (+ (chop (sum) -53) (expt 2 53)))))
  :hints (("Goal" :nonlinearp t :use (sum-a-38) :in-theory (enable chop))))

(local-defthmd sum-a-40
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (not (integerp (* (expt 2 -53) (- (sigaprime) (* (expt 2 (- (n))) (x0)))))))
  :hints (("Goal" :use (sum-a-cin-4 sum-a-34))))

(local-defthmd sum-a-41
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (not (= (* (expt 2 -53) (chop (sum) -53))
	           (* (expt 2 -53) (- (sigaprime) (* (expt 2 (- (n))) (x0)))))))
  :hints (("Goal" :use (sum-a-40) :in-theory (enable chop))))

(local-defthmd sum-a-42
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (not (= (chop (sum) -53)
	           (- (sigaprime) (* (expt 2 (- (n))) (x0))))))
  :hints (("Goal" :use (sum-a-41) :in-theory (theory 'minimal-theory))))

(local-defthmd sum-a-43
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (and (< (chop (sum) -53)
	           (- (sigaprime) (* (expt 2 (- (n))) (x0))))
	        (< (- (sigaprime) (* (expt 2 (- (n))) (x0)))
		   (+ (chop (sum) -53) (expt 2 53)))))
  :hints (("Goal" :in-theory (enable chop) :use (sum-a-42 sum-a-39))))

(local-defthmd sum-a-44
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (and (< (absval (explp) (chop (sum) -53))
	           (- (absval (explp) (sigaprime)) (absval (explp) (* (expt 2 (- (n))) (x0)))))
	        (< (- (absval (explp) (sigaprime)) (absval (explp) (* (expt 2
  (- (n))) (x0))))
		   (absval (explp) (+ (chop (sum) -53) (expt 2 53))))))
  :hints (("Goal" :use (sum-a-43) :in-theory (enable absval) :nonlinearp t)))

(local-defthm sum-a-45
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (equal (absval (explp) (sigaprime))
                  (abs (a))))
  :hints (("Goal" :use (sum-1-12)
                  :in-theory (e/d (far-rewrite absval explp sigaprime-rewrite opbgeopa expl-rewrite) (abs)))))

(local-defthmd sum-a-46
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1))
           (and (< (absval (explp) (chop (sum) -53))
	           (- (abs (a)) (abs (b))))
	        (< (- (abs (a)) (abs (b)))
		   (absval (explp) (+ (chop (sum) -53) (expt 2 53))))))
  :hints (("Goal" :use (sum-a-44 sum-a-45 sum-a-18) :in-theory (e/d (sum-a-16) (abs)))))

(local-defthmd sum-a-47
  (implies (and (= (mulovfl) 0) (= (opbgeopa) 0) (= (usa) 1))
	   (equal (abs (+ (a) (b)))
	          (- (abs (a)) (abs (b)))))
  :hints (("Goal" :in-theory (enable absval bp usa-rewrite a val opbgeopa-b>=a)
                  :nonlinearp t
                  :use (signa-0-1 signb-0-1 absval-a>=0 absval-b>=0 expb-0-b expb-pos-b))))

(local-defthmd sum-1-a
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
	        (< (abs (+ (a) (b)))
		   (absval (explp) (+ (chop (sum) -53) (expt 2 53))))))
  :hints (("Goal" :use (sum-1-a-lsa sum-a-47 sum-a-46))))

(local-defthmd sum-bounds-b-1
  (implies (and (integerp a) (integerp b) (= (bits a 52 0) 0))
           (equal (bits (+ b a) 52 0)
	          (bits b 52 0)))
  :hints (("Goal" :use ((:instance mod-sum (n (expt 2 53)) (b a) (a b))
                        (:instance bits-bits (x b) (i 52) (j 0) (k 52) (l 0)))
		  :in-theory (enable bits))))

(local-defthmd sum-bounds-b-2
  (implies (and (integerp a) (integerp b) (= (bits a 52 0) 0))
           (equal (bits (- b a) 52 0)
	          (bits b 52 0)))
  :hints (("Goal" :use ((:instance mod-diff (n (expt 2 53)) (b a) (a b))
                        (:instance bits-bits (x b) (i 52) (j 0) (k 52) (l 0)))
		  :in-theory (enable bits))))

(local-defthmd sum-bounds-b-3
  (implies (and (integerp a) (integerp b) (= (bits a 52 0) 0) (not (= (bits b 52 0) 0)))
           (not (equal (bits (- a b) 52 0) 0)))
  :hints (("Goal" :use ((:instance mod-0-int (m b) (n (expt 2 53)))
			(:instance mod-0-int (m b) (n (expt 2 53)))
                        (:instance mod-0-int (m (- a b)) (n (expt 2 53))))
		  :in-theory (enable bits))))

(local-defthm sum-bounds-b-4
  (implies (and (= (mulovfl) 0) (not (= (stk) 1)))
           (and (equal (mulstk) 0)
	        (equal (shiftout) 0)))
  :hints (("Goal" :use (near-shiftout-0)
                  :in-theory (enable stk* add-lemma))))

(local-defthmd sum-bounds-b-5
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 0) (not (= (stk) 1)))
	   (not (equal (bits (sum) 52 0) 0)))
  :hints (("Goal" :in-theory (enable sum-1-5)
                  :use (sum-1-8
		        (:instance sum-bounds-b-1 (a (siga)) (b (sigb)))
			(:instance bits-bits (x (siga)) (i 53) (j 0) (k 52) (l 0))))))

(local-defthm sum-bounds-b-6
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 1) (= (usa) 1) (not (= (stk) 1)))
	   (not (equal (bits (sum) 52 0) 0)))
  :hints (("Goal" :in-theory (enable sum-1-21)
                  :use (sum-1-8
		        (:instance sum-bounds-b-2 (a (siga)) (b (sigb)))
			(:instance bits-bits (x (siga)) (i 53) (j 0) (k 52) (l 0))))))

(local-defthm sum-bounds-b-7
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0) (not (= (stk) 1)))
	   (equal (sum) (+ (siga) (* (expt 2 (- (expdiff))) (sigb)))))
  :hints (("Goal" :in-theory (enable sum-lsa-8 sigl sigs sigaprime-rewrite sigbprime-rewrite))))

(local-defthm sum-bounds-b-8
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 0) (not (= (stk) 1)))
	   (not (equal (bits (sum) 52 0) 0)))
  :hints (("Goal" :in-theory (e/d (sum-bounds-b-7) (bits-bits))
                  :use (sum-1-8 shiftout-rewrite
		        (:instance bits-bits (x (sigb)) (i (+ (expdiff) 52)) (j 0) (k 52) (l 0))
		        (:instance bits-shift-up-2 (x (* (expt 2 (- (expdiff))) (sigb)))
			                           (i 52) (k (expdiff)))
		        (:instance sum-bounds-b-1 (a (siga)) (b (* (expt 2 (- (expdiff))) (sigb))))
			(:instance bits-bits (x (siga)) (i 53) (j 0) (k 52) (l 0))))))

(local-defthm sum-bounds-b-9
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (= (stk) 1)))
	   (equal (bits (sigaprime) 52 0) 0))
  :hints (("Goal" :in-theory (e/d (sum-1-8 sum-bounds-b-7 sigaprime-rewrite) (bits-bits))
                  :use ((:instance bits-shift-up-2 (x (siga)) (i 51) (k 1))
			(:instance bits-bits (x (siga)) (i 53) (j 0) (k 52) (l 0))
			(:instance bits-bits (x (siga)) (i 53) (j 0) (k 51) (l 0))))))

(local-defthmd sum-bounds-b-10
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (= (stk) 1)))
	   (integerp (* (expt 2 (- (n))) (sigb))))
  :hints (("Goal" :in-theory (enable sigshft-rewrite far-rewrite)
                  :use (sum-a-17 shiftout-rewrite))))

(local-defthmd sum-bounds-b-11
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (= (stk) 1)))
	   (not (equal (bits (* (expt 2 (- (n))) (sigb)) 52 0) 0)))
  :hints (("Goal" :in-theory (e/d (sum-bounds-b-7) (bits-bits))
                  :use (sum-bounds-b-10
		        (:instance bits-bits (x (sigb)) (i (+ (n) 52)) (j 0) (k 52) (l 0))
		        (:instance bits-shift-up-2 (x (* (expt 2 (- (n))) (sigb)))
			                           (i 52) (k (n)))))))

(local-defthm sum-bounds-b-12
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
                (= (opbgeopa) 0) (= (usa) 1) (not (= (stk) 1)))
	   (not (equal (bits (sum) 52 0) 0)))
  :hints (("Goal" :in-theory (enable sum-a-cin-11)
                  :use (sum-bounds-b-9 sum-bounds-b-10 sum-bounds-b-11
		        (:instance sum-bounds-b-3 (a (sigaprime)) (b (* (expt 2 (- (n))) (sigb))))))))

(local-defthm sum-bounds-b
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
	   (or (= (stk) 1)
	       (not (equal (bits (sum) 52 0) 0))))
  :rule-classes ()
  :hints (("Goal" :use (sum-bounds-b-5 sum-bounds-b-6 sum-bounds-b-8 sum-bounds-b-12))))

(defthm sum-bounds-1
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
	        (< (abs (+ (a) (b)))
		   (absval (explp) (+ (chop (sum) -53) (expt 2 53))))
		(or (= (stk) 1)
	            (not (equal (bits (sum) 52 0) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (sum-1-b sum-1-a sum-bounds-b))))












(local-defthm sum-usa-31
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 1))
           (equal (sum) (bits (+ (sigl) 1 (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-usa-32
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 1))
           (equal (sum) (bits (- (sigl) (sigshft)) 107 0)))
  :hints (("Goal" :in-theory (enable sum-usa-31 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (sigshft))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthmd sum-usa-33
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 1))
           (equal (sum) (- (sigl) (sigshft))))
  :hints (("Goal" :in-theory (enable sum-usa-32 bvecp)
                  :use (bvecp-sigl sum-usa-13))))

(local-defthm sum-usa-40
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0))
           (equal (sum) (bits (+ (sigl) (bits (lognot (sigshft)) 107 0)) 107 0)))
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd sum-usa-41
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0))
           (equal (sum) (bits (- (sigl) (1+ (sigshft))) 107 0)))
  :hints (("Goal" :in-theory (enable sum-usa-40 bits-lognot bvecp)
                  :use (bvecp-sigshft
		        (:instance bits-plus-mult-2 (x (- (sigl) (1+ (sigshft)))) (y 1) (k 108) (n 107) (m 0))))))

(local-defthm sum-usa-42
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (= (expb) 0))
           (< (sigb) (siga)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat opbgeopa sigb siga bvecp)
                  :use (bvecp-fraca bvecp-fracb))))

(local-defthm sum-usa-43
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (= (expb) 0))
           (< (sigs) (sigl)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigs sigl sigaprime-rewrite sigbprime-rewrite)
           :use (sum-usa-42))))

(local-defthm sum-usa-44-a
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (= (expb) 0))
           (< (sigshft) (sigl)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigshft-rewrite)
                  :nonlinearp t
                  :use (sum-usa-43))))

(local-defthm sum-usa-44-b
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (> (expb) 0) (= (expdiff) 0))
           (and (= (expa) (expb))
	        (< (sigbprime) (sigaprime))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :in-theory (enable sigaprime sigbprime siga sigb cat opbgeopa expdiff-rewrite))))

(local-defthm sum-usa-44-c
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (> (expb) 0) (= (expdiff) 0))
           (< (sigshft) (sigl)))
  :rule-classes ()
  :hints (("Goal" :use (sum-usa-44-b)
                  :in-theory (enable sigshft-rewrite sigs sigl opbgeopa))))

(local-defthm sum-usa-44-d
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (> (expb) 0) (> (expdiff) 0))
           (< (sigs) (* 2 (sigl))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable opbgeopa siga sigb bvecp cat)
                  :nonlinearp t
                  :use (sigs sigl sigaprime sigbprime sigb-bounds sigb-expb-0 siga-bounds
		        siga-expa-0 bvecp-fraca bvecp-fraca))))

(local-defthm sum-usa-44-e
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0) (> (expb) 0) (> (expdiff) 0))
           (< (sigshft) (sigl)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigshft-rewrite)
                  :nonlinearp t
                  :use (sum-usa-44-d))))

(local-defthm sum-usa-44
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0))
           (< (sigshft) (sigl)))
  :rule-classes ()
  :hints (("Goal" :use (sum-usa-44-a sum-usa-44-c sum-usa-44-e))))

(local-defthmd sum-usa-45
  (implies (and (= (mulovfl) 0) (= (usa) 1) (= (shiftout) 0) (= (mulstk) 1) (= (opbgeopa) 0))
           (equal (sum) (- (sigl) (1+ (sigshft)))))
  :hints (("Goal" :in-theory (enable sum-usa-41 bvecp)
                  :use (sum-usa-44 bvecp-sigl))))

(defthmd sum-rewrite
  (implies (= (mulovfl) 0)
           (equal (sum)
	          (if (= (usa) 0)
		      (+ (sigl) (sigshft))
		    (if (and (= (shiftout) 0) (or (= (mulstk) 0) (= (opbgeopa) 1)))
		        (- (sigl) (sigshft))
		      (- (sigl) (1+ (sigshft)))))))
  :hints (("Goal" :use (sum-lsa-4 sum-usa-15 sum-usa-26 sum-usa-33 sum-usa-45 near-shiftout-0)
                  :in-theory (enable far opbgeopa add-lemma stk* mulstk shiftout usa))))

