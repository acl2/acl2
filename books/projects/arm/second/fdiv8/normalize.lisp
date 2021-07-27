(in-package "RTL")

(include-book "clz")

(local-defund siga-1 ()
  (case (fnum)
    (2 (mana))
    (1 (setbits (bits 0 52 0) 53 51 29 (mana)))
    (0 (setbits (bits 0 52 0) 53 51 42 (mana)))
    (t (bits 0 52 0))))

(local-defund sigb-1 ()
  (case (fnum)
    (2 (manb))
    (1 (setbits (bits 0 52 0) 53 51 29 (manb)))
    (0 (setbits (bits 0 52 0) 53 51 42 (manb)))
    (t (bits 0 52 0))))

(local-defund bs* ()
  (case (fnum)
    (2 1023)
    (1 127)
    (0 15)
    (t 0)))

(local-defund siga* ()
  (if1 (log= (expa) 0)
       (bits (ash (siga-1) (bits (clz53 (siga-1)) 5 0)) 52 0)
       (setbitn (siga-1) 53 52 1)))

(local-defund expashft ()
  (if1 (log= (expa) 0)
       (bits (- 1 (bits (clz53 (siga-1)) 5 0)) 12 0)
       (expa)))

(local-defund sigb* ()
  (if1 (log= (expb) 0)
       (bits (ash (sigb-1) (bits (clz53 (sigb-1)) 5 0)) 52 0)
       (setbitn (sigb-1) 53 52 1)))

(local-defund expbshft ()
  (if1 (log= (expb) 0)
       (bits (- 1 (bits (clz53 (sigb-1)) 5 0)) 12 0)
       (expb)))

(local-defund expdiff* ()
  (bits (+ (- (si (expashft) 13) (si (expbshft) 13)) (bs*)) 12 0))

(local-in-theory (disable (siga-1) (sigb-1) (bs*) (siga*) (sigb*) (expashft) (expbshft) (expdiff*)))

(local-defthmd normalize-lemma
  (and (equal (siga) (siga*))
       (equal (sigb) (sigb*))
       (equal (expdiff) (expdiff*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(normalize siga sigb expdiff siga-1 sigb-1 bs*
                                         siga* expashft sigb* expbshft expdiff*))))

(defthm integerp-sigb
  (integerp (sigb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable normalize-lemma sigb*))))

(defthm integerp-siga
  (integerp (siga))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable normalize-lemma siga*))))

(defund a () (decode (opaw) (f)))

(defund b () (decode (opbw) (f)))

(defund p () (prec (f)))

(defund e () (expw (f)))

(defund bs () (bias (f)))

(in-theory (disable (a) (b) (p) (e) (bs)))

(local-defthm bs*-rewrite
  (equal (bs*) (bias (f)))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable hp sp dp bias expw f bs*))))

(defthm opz-opw
  (implies (not (specialp))
           (and (equal (opaz) (opaw))
	        (equal (opbz) (opbw))))
  :hints (("Goal" :in-theory (enable specialp))))

(defthmd spec-fields
  (implies (not (specialp))
           (and (equal (sgnf (opaw) (f)) (signa))
	        (equal (expf (opaw) (f)) (expa))
		(equal (manf (opaw) (f)) (mana))
	        (equal (sgnf (opbw) (f)) (signb))
	        (equal (expf (opbw) (f)) (expb))
		(equal (manf (opbw) (f)) (manb))))
  :hints (("Goal" :use (a-fields b-fields) :in-theory (enable specialp))))
		
(defthm spec-class
  (implies (not (specialp))
           (and (or (normp (opaw) (f))
	            (denormp (opaw) (f)))
		(or (normp (opbw) (f))
	            (denormp (opbw) (f)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable specialp)
                  :use (member-classa member-classb a-class b-class))))

(local-defthm a-normp
  (implies (and (not (specialp))
                (not (= (expa) 0)))
	   (normp (opaw) (f)))
  :hints (("Goal" :use (spec-class spec-fields)
                  :in-theory (enable denormp))))

(local-defthm a-denormp
  (implies (and (not (specialp))
                (= (expa) 0))
	   (denormp (opaw) (f)))
  :hints (("Goal" :use (spec-class spec-fields)
                  :in-theory (enable normp))))

(defthmd bvecp-mana
  (implies (not (specialp))
           (bvecp (mana) (sigw (f))))
  :hints (("Goal" :in-theory (enable manf sigw f hp sp dp)
                  :use (spec-fields fnum-vals))))
		  
(defthmd bvecp-expa
  (implies (not (specialp))
           (bvecp (expa) (expw (f))))
  :hints (("Goal" :in-theory (enable expf expw f hp sp dp)
                  :use (spec-fields fnum-vals))))

(local-defthm siga-1-rewrite
  (implies (not (specialp))
           (equal (siga-1)
	          (* (expt 2 (- 52 (sigw (f))))
		     (mana))))
  :hints (("Goal" :in-theory (enable bvecp cat siga-1 sigw f hp sp dp)
                  :use (bvecp-mana fnum-vals))))

(local-defthm siga-normp
  (implies (and (not (specialp))
                (not (= (expa) 0)))
	   (equal (siga) (* (expt 2 52) (sig (a)))))
  :hints (("Goal" :in-theory (enable bvecp a cat normalize-lemma siga* f hp sp dp ndecode decode manf prec)
                  :use (spec-fields a-normp bvecp-mana fnum-vals a-normp (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthm bvecp-siga-1
  (implies (and (not (specialp))
                (= (expa) 0))
           (bvecp (siga-1) 53))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable denormp bvecp cat siga-1 sigw sigf f hp sp dp)
                  :use (a-denormp bvecp-mana fnum-vals))))

(local-defthm siga-1-pos
  (implies (and (not (specialp))
                (= (expa) 0))
           (not (= (siga-1) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable manf specialp denormp bvecp cat siga-1 sigw sigf f hp sp dp)
                  :use (a-fields bvecp-mana a-denormp fnum-vals))))

(local-defthmd clz-siga-1
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (bits (clz53 (siga-1)) 5 0)
	          (- 52 (expo (siga-1)))))
  :hints (("Goal" :use (bvecp-siga-1 siga-1-pos
                        (:instance expo<= (x (siga-1)) (n 52))
                        (:instance expo>= (x (siga-1)) (n 1))
                        (:instance clz-expo (s (siga-1))))
                  :in-theory (enable bvecp))))

(local-in-theory (disable siga-1-rewrite))

(local-defthmd siga-siga-1
  (implies (and (not (specialp))
                (= (expa) 0))
           (equal (siga)
	          (* (expt 2 (- 52 (expo (siga-1))))
		     (siga-1))))
  :hints (("Goal" :in-theory (enable ash bvecp clz-siga-1 siga*)
                  :nonlinearp t
                  :use (siga-1-pos bvecp-siga-1 normalize-lemma
		        (:instance expo<= (x (siga-1)) (n 52))
		        (:instance expo-upper-bound (x (siga-1)))))))

(local-defthmd siga-mana
  (implies (and (not (specialp))
                (= (expa) 0))
           (equal (siga)
	          (* (expt 2 (- 52 (expo (mana))))
		     (mana))))
  :hints (("Goal" :in-theory (enable siga-siga-1 siga-1-rewrite f dp sp hp sigw)
                  :use (bvecp-siga-1 siga-1-pos fnum-vals
		        (:instance expo-shift (x (mana)) (n (- 52 (sigw (f)))))))))

(local-defthmd siga-sig-mana
  (implies (and (not (specialp))
                (= (expa) 0))
           (equal (siga)
	          (* (expt 2 52) (sig (mana)))))
  :hints (("Goal" :in-theory (enable siga-mana)
                  :use (bvecp-mana
		        (:instance fp-abs (x (mana)))))))

(local-defthm siga-denormp
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (siga) (* (expt 2 52) (sig (a)))))
  :hints (("Goal" :in-theory (enable siga-sig-mana manf specialp a decode prec f dp sp hp sigf) 
                  :use (fnum-vals a-denormp a-fields (:instance sig-ddecode (x (opaw)) (f (f)))))))

(defthmd siga-rewrite
  (implies (not (specialp))
	   (equal (siga) (* (expt 2 52) (sig (a)))))
  :hints (("Goal" :use (siga-normp siga-denormp))))

(local-defthmd clz-mana
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (bits (clz53 (siga-1)) 5 0)
	          (- (sigw (f)) (expo (mana)))))
  :hints (("Goal" :in-theory (enable clz-siga-1 dp sp hp prec f sigw)
		  :use (fnum-vals bvecp-mana siga-1-pos siga-1-rewrite 
		        (:instance expo-shift (x (mana)) (n (- 52 (sigw (f)))))))))

(local-defthmd expashft-denorm
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (expashft)
	          (bits (1+ (- (expo (mana)) (sigw (f)))) 12 0)))
  :hints (("Goal" :in-theory (enable clz-mana expashft))))

(local-defthmd si-expashft-denorm
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (si (expashft) 13)
	          (+ (expo (a)) (bias (f)))))
  :hints (("Goal" :in-theory (enable manf specialp a sigf prec decode expashft-denorm bvecp dp sp hp f)
                  :use (bvecp-mana fnum-vals a-denormp a-fields
		        (:instance expo-ddecode (x (opaw)) (f (f)))
		        (:instance si-bits (x (1+ (- (expo (mana)) (sigw (f))))) (n 13))
		        (:instance expo<= (x (mana)) (n (1- (sigw (f)))))
		        (:instance expo>= (x (mana)) (n 0))))))

(local-defthmd si-expashft-norm
  (implies (and (not (specialp))
                (not (= (expa) 0)))
	   (equal (si (expashft) 13)
	          (+ (expo (a)) (bias (f)))))
  :hints (("Goal" :in-theory (enable expf expw specialp a si decode expashft bvecp dp sp hp f)
                  :use (bvecp-expa fnum-vals a-normp a-fields
		        (:instance expo-ndecode (x (opaw)) (f (f)))
		        (:instance si-bits (x (expa)) (n 13))
		        (:instance expo<= (x (expa)) (n (1- (expw (f)))))
		        (:instance expo>= (x (expa)) (n 0))))))

(local-defthmd si-expashft
  (implies (not (specialp))
	   (equal (si (expashft) 13)
	          (+ (expo (a)) (bias (f)))))
  :hints (("Goal" :use (si-expashft-denorm si-expashft-norm))))

(local-defthm b-normp
  (implies (and (not (specialp))
                (not (= (expb) 0)))
	   (normp (opbw) (f)))
  :hints (("Goal" :use (spec-class spec-fields)
                  :in-theory (enable denormp))))

(local-defthm b-denormp
  (implies (and (not (specialp))
                (= (expb) 0))
	   (denormp (opbw) (f)))
  :hints (("Goal" :use (spec-class spec-fields)
                  :in-theory (enable normp))))

(defthmd bvecp-manb
  (implies (not (specialp))
           (bvecp (manb) (sigw (f))))
  :hints (("Goal" :in-theory (enable manf sigw f hp sp dp)
                  :use (spec-fields fnum-vals))))
		  
(defthmd bvecp-expb
  (implies (not (specialp))
           (bvecp (expb) (expw (f))))
  :hints (("Goal" :in-theory (enable expf expw f hp sp dp)
                  :use (spec-fields fnum-vals))))

(local-defthm sigb-1-rewrite
  (implies (not (specialp))
           (equal (sigb-1)
	          (* (expt 2 (- 52 (sigw (f))))
		     (manb))))
  :hints (("Goal" :in-theory (enable bvecp cat sigb-1 sigw f hp sp dp)
                  :use (bvecp-manb fnum-vals))))

(defthmd integerp-sigb-shift
  (implies (not (specialp))
           (integerp (* (expt 2 (- 53 (p))) (sigb))))
  :hints (("Goal" :in-theory (enable p sigw f dp sp hp normalize-lemma sigb*)
           :use (fnum-vals))))

(local-defthm sigb-normp
  (implies (and (not (specialp))
                (not (= (expb) 0)))
	   (equal (sigb) (* (expt 2 52) (sig (b)))))
  :hints (("Goal" :in-theory (enable bvecp b cat normalize-lemma sigb* f hp sp dp ndecode decode manf prec)
                  :use (spec-fields b-normp bvecp-manb fnum-vals b-normp (:instance sig-ndecode (x (opbw)) (f (f)))))))

(local-defthm bvecp-sigb-1
  (implies (and (not (specialp))
                (= (expb) 0))
           (bvecp (sigb-1) 53))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable denormp bvecp cat sigb-1 sigw sigf f hp sp dp)
                  :use (b-denormp bvecp-manb fnum-vals))))

(local-defthm sigb-1-pos
  (implies (and (not (specialp))
                (= (expb) 0))
           (not (= (sigb-1) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable manf specialp denormp bvecp cat sigb-1 sigw sigf f hp sp dp)
                  :use (b-fields bvecp-manb b-denormp fnum-vals))))

(local-defthmd clz-sigb-1
  (implies (and (not (specialp))
                (= (expb) 0))
	   (equal (bits (clz53 (sigb-1)) 5 0)
	          (- 52 (expo (sigb-1)))))
  :hints (("Goal" :use (bvecp-sigb-1 sigb-1-pos
                        (:instance expo<= (x (sigb-1)) (n 52))
                        (:instance expo>= (x (sigb-1)) (n 1))
                        (:instance clz-expo (s (sigb-1))))
                  :in-theory (enable bvecp))))

(local-in-theory (disable sigb-1-rewrite))

(local-defthmd sigb-sigb-1
  (implies (and (not (specialp))
                (= (expb) 0))
           (equal (sigb)
	          (* (expt 2 (- 52 (expo (sigb-1))))
		     (sigb-1))))
  :hints (("Goal" :in-theory (enable ash bvecp clz-sigb-1 sigb*)
                  :nonlinearp t
                  :use (sigb-1-pos bvecp-sigb-1 normalize-lemma
		        (:instance expo<= (x (sigb-1)) (n 52))
		        (:instance expo-upper-bound (x (sigb-1)))))))

(local-defthmd sigb-manb
  (implies (and (not (specialp))
                (= (expb) 0))
           (equal (sigb)
	          (* (expt 2 (- 52 (expo (manb))))
		     (manb))))
  :hints (("Goal" :in-theory (enable sigb-sigb-1 sigb-1-rewrite f dp sp hp sigw)
                  :use (bvecp-sigb-1 sigb-1-pos fnum-vals
		        (:instance expo-shift (x (manb)) (n (- 52 (sigw (f)))))))))

(local-defthmd sigb-sig-manb
  (implies (and (not (specialp))
                (= (expb) 0))
           (equal (sigb)
	          (* (expt 2 52) (sig (manb)))))
  :hints (("Goal" :in-theory (enable sigb-manb)
                  :use (bvecp-manb
		        (:instance fp-abs (x (manb)))))))

(local-defthm sigb-denormp
  (implies (and (not (specialp))
                (= (expb) 0))
	   (equal (sigb) (* (expt 2 52) (sig (b)))))
  :hints (("Goal" :in-theory (enable sigb-sig-manb manf specialp b decode prec f dp sp hp sigf) 
                  :use (fnum-vals b-denormp b-fields (:instance sig-ddecode (x (opbw)) (f (f)))))))

(defthmd sigb-rewrite
  (implies (not (specialp))
	   (equal (sigb) (* (expt 2 52) (sig (b)))))
  :hints (("Goal" :use (sigb-normp sigb-denormp))))

(local-defthmd clz-manb
  (implies (and (not (specialp))
                (= (expb) 0))
	   (equal (bits (clz53 (sigb-1)) 5 0)
	          (- (sigw (f)) (expo (manb)))))
  :hints (("Goal" :in-theory (enable clz-sigb-1 dp sp hp prec f sigw)
		  :use (fnum-vals bvecp-manb sigb-1-pos sigb-1-rewrite 
		        (:instance expo-shift (x (manb)) (n (- 52 (sigw (f)))))))))

(local-defthmd expbshft-denorm
  (implies (and (not (specialp))
                (= (expb) 0))
	   (equal (expbshft)
	          (bits (1+ (- (expo (manb)) (sigw (f)))) 12 0)))
  :hints (("Goal" :in-theory (enable clz-manb expbshft))))

(local-defthmd si-expbshft-denorm
  (implies (and (not (specialp))
                (= (expb) 0))
	   (equal (si (expbshft) 13)
	          (+ (expo (b)) (bias (f)))))
  :hints (("Goal" :in-theory (enable manf specialp b sigf prec decode expbshft-denorm bvecp dp sp hp f)
                  :use (bvecp-manb fnum-vals b-denormp b-fields
		        (:instance expo-ddecode (x (opbw)) (f (f)))
		        (:instance si-bits (x (1+ (- (expo (manb)) (sigw (f))))) (n 13))
		        (:instance expo<= (x (manb)) (n (1- (sigw (f)))))
		        (:instance expo>= (x (manb)) (n 0))))))

(local-defthmd si-expbshft-norm
  (implies (and (not (specialp))
                (not (= (expb) 0)))
	   (equal (si (expbshft) 13)
	          (+ (expo (b)) (bias (f)))))
  :hints (("Goal" :in-theory (enable expf expw specialp b si decode expbshft bvecp dp sp hp f)
                  :use (bvecp-expb fnum-vals b-normp b-fields
		        (:instance expo-ndecode (x (opbw)) (f (f)))
		        (:instance si-bits (x (expb)) (n 13))
		        (:instance expo<= (x (expb)) (n (1- (expw (f)))))
		        (:instance expo>= (x (expb)) (n 0))))))

(local-defthmd si-expbshft
  (implies (not (specialp))
	   (equal (si (expbshft) 13)
	          (+ (expo (b)) (bias (f)))))
  :hints (("Goal" :use (si-expbshft-denorm si-expbshft-norm))))

(defthmd expdiff-rewrite
  (implies (not (specialp))
	   (equal (expdiff)
	          (bits (+ (- (expo (a)) (expo (b))) (bias (f))) 12 0)))
  :hints (("Goal" :in-theory (enable si-expashft si-expbshft expdiff*)
                  :use (normalize-lemma))))

(defthm nrepp-drepp
  (implies (not (specialp))
           (and (or (nrepp (a) (f))
	            (drepp (a) (f)))
		(or (nrepp (b) (f))
	            (drepp (b) (f)))))
  :rule-classes ()
  :hints (("Goal" :use (a-fields b-fields a-normp a-denormp b-normp b-denormp)
                  :in-theory (enable specialp decode a b))))

(defthmd si-expdiff-rewrite
  (implies (not (specialp))
	   (equal (si (expdiff) 13)
	          (+ (- (expo (a)) (expo (b))) (bias (f)))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite nrepp drepp f dp sp hp bias expw prec)
                  :use (nrepp-drepp (:instance si-bits (x (+ (- (expo (a)) (expo (b))) (bias (f)))) (n 13))))))

(defthm rationalp-abs
  (implies (rationalp x) (rationalp (abs x)))
  :rule-classes (:type-prescription :rewrite))

(defthmd a-b-not-zero
  (implies (not (specialp))
           (and (not (zerop (a)))
	        (not (zerop (b)))))
  :hints (("Goal" :in-theory (enable nrepp drepp) :use (nrepp-drepp))))

(local-defthmd quotient-formula-1
  (implies (not (specialp))
           (equal (/ (* (sig (a)) (expt 2 (expo (a))))
	             (* (sig (b)) (expt 2 (expo (b)))))
	          (* (sig (a))
                     (/ (sig (b)))
                     (expt 2 (+ (expo (a)) (- (expo (b))))))))
  :hints (("Goal" :use (a-b-not-zero))))

(local-defthmd quotient-formula-2
  (implies (not (specialp))
           (equal (/ (abs (a)) (abs (b)))
	          (* (expt 2 (- (si (expdiff) 13) (bias (f))))
		     (/ (siga) (sigb)))))
  :hints (("Goal" :in-theory (e/d (si-expdiff-rewrite siga-rewrite sigb-rewrite) (abs))
                  :use (a-b-not-zero
		        (:instance fp-abs (x (a)))
		        (:instance fp-abs (x (b)))))
	  ("Goal'''" :use (quotient-formula-1) :in-theory (theory 'minimal-theory))))

(defthmd quotient-formula
  (implies (not (specialp))
           (equal (abs (/ (a) (b)))
	          (* (expt 2 (- (si (expdiff) 13) (bias (f))))
		     (/ (siga) (sigb)))))
  :hints (("Goal" :use (quotient-formula-2))))

(defthmd exactp-a
  (implies (not (specialp))
           (integerp (* (expt 2 (1- (p))) (sig (a)))))
  :hints (("Goal" :in-theory (enable exactp f dp sp hp p prec sigw nrepp drepp)
                  :use (nrepp-drepp
		        (:instance exactp-<= (x (a)) (m (+ (1- (p)) (bias (f)) (expo (a)))) (n (p)))))))

(defthmd exactp-siga
  (implies (not (specialp))
           (integerp (* (expt 2 (- (p) 53)) (siga))))
  :hints (("Goal" :in-theory (enable siga-rewrite)
                  :use (exactp-a))))

(defthmd exactp-b
  (implies (not (specialp))
           (integerp (* (expt 2 (1- (p))) (sig (b)))))
  :hints (("Goal" :in-theory (enable exactp f dp sp hp p prec sigw nrepp drepp)
                  :use (nrepp-drepp
		        (:instance exactp-<= (x (b)) (m (+ (1- (p)) (bias (f)) (expo (b)))) (n (p)))))))

(defthmd exactp-sigb
  (implies (not (specialp))
           (integerp (* (expt 2 (- (p) 53)) (sigb))))
  :hints (("Goal" :in-theory (enable sigb-rewrite)
                  :use (exactp-b))))

(defthmd si-expdiff-bounds
  (implies (not (specialp))
	   (and (< (si (expdiff) 13) (expt 2 12))
	        (> (si (expdiff) 13) (- 2 (expt 2 12)))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite nrepp drepp f dp sp hp bias expw prec)
                  :use (nrepp-drepp (:instance si-bits (x (+ (- (expo (a)) (expo (b))) (bias (f)))) (n 13))))))
		  
