(in-package "RTL")

(include-book "clz")

(local-defund siga-1 ()
  (case (fnum)
    (2 (mana))
    (1 (setbits (bits 0 52 0) 53 51 29 (mana)))
    (0 (setbits (bits 0 52 0) 53 51 42 (mana)))
    (t (bits 0 52 0))))

(local-defund bs* ()
  (case (fnum)
    (2 1023)
    (1 127)
    (0 15)
    (t 0)))

(local-defund siga* ()
  (if1 (log= (si (expa) 13) 0)
       (bits (ash (siga-1) (bits (clz53 (siga-1)) 5 0)) 52 0)
       (setbitn (siga-1) 53 52 1)))

(local-defund expshft* ()
  (if1 (log= (si (expa) 13) 0)
       (bits (- 1 (bits (clz53 (siga-1)) 5 0)) 12 0)
       (expa)))

(local-defund expq* ()
  (bits (bits (+ (si (expshft*) 13) (bs*)) 11 0) 11 1))

(local-in-theory (disable (siga-1) (bs*) (siga*) (expshft*) (expq*)))

(local-defthmd normalize-lemma
  (and (equal (siga) (siga*))
       (equal (expshft) (expshft*))
       (equal (expq) (expq*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(normalize siga expshft expq siga-1 bs* siga* expshft* expq*))))

(defthm integerp-siga
  (integerp (siga))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable normalize-lemma siga*))))

(defund a () (decode (opaw) (f)))

(defund p () (prec (f)))

(defund e () (expw (f)))

(defund bs () (bias (f)))

(in-theory (disable (a) (p) (e) (bs)))

(local-defthm bs*-rewrite
  (equal (bs*) (bias (f)))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable hp sp dp bias expw f bs*))))

(defthm opz-opw
  (implies (not (specialp))
           (equal (opaz) (opaw)))
  :hints (("Goal" :in-theory (enable specialp))))

(defthmd spec-fields
  (implies (not (specialp))
           (and (equal (sgnf (opaw) (f)) (signa))
	        (equal (expf (opaw) (f)) (expa))
		(equal (manf (opaw) (f)) (mana))))
  :hints (("Goal" :use (a-fields) :in-theory (enable specialp))))
		
(defthm spec-class
  (implies (not (specialp))
           (or (normp (opaw) (f))
	       (denormp (opaw) (f))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable specialp)
                  :use (member-classa a-class))))

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
  :hints (("Goal" :in-theory (enable si bvecp a cat normalize-lemma siga* f hp sp dp ndecode decode manf prec)
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

(defthmd siga-mana
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

(in-theory (disable sgn-ddecode))

(defthmd a-pos
  (implies (not (specialp))
           (> (a) 0))
  :hints (("Goal" :in-theory (enable sgn specialp encodingp normp denormp decode a f dp sp hp prec p)
                  :use (signa-0-1 a-fields member-classa a-class fnum-vals a-fields
		        (:instance sgn-ndecode (x (opaw)) (f (f)))
		        (:instance sgn-ddecode (x (opaw)) (f (f)))))))

(defthmd siga-bounds
  (implies (not (specialp))
	   (and (<= (expt 2 52) (siga))
	        (< (siga) (expt 2 53))))
  :hints (("Goal" :use (a-pos
                        (:instance sig-upper-bound (x (a)))
                        (:instance sig-lower-bound (x (a))))
	          :in-theory (enable siga-rewrite)
		  :nonlinearp t)))

(local-defthmd clz-mana
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (bits (clz53 (siga-1)) 5 0)
	          (- (sigw (f)) (expo (mana)))))
  :hints (("Goal" :in-theory (enable clz-siga-1 dp sp hp prec f sigw)
		  :use (fnum-vals bvecp-mana siga-1-pos siga-1-rewrite 
		        (:instance expo-shift (x (mana)) (n (- 52 (sigw (f)))))))))

(local-defthmd expshft-denorm
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (expshft)
	          (bits (1+ (- (expo (mana)) (sigw (f)))) 12 0)))
  :hints (("Goal" :in-theory (enable clz-mana expshft* normalize-lemma))))

(local-defthmd si-expshft-denorm
  (implies (and (not (specialp))
                (= (expa) 0))
	   (equal (si (expshft) 13)
	          (+ (expo (a)) (bias (f)))))
  :hints (("Goal" :in-theory (enable manf specialp a sigf prec decode expshft-denorm bvecp dp sp hp f)
                  :use (bvecp-mana fnum-vals a-denormp a-fields
		        (:instance expo-ddecode (x (opaw)) (f (f)))
		        (:instance si-bits (x (1+ (- (expo (mana)) (sigw (f))))) (n 13))
		        (:instance expo<= (x (mana)) (n (1- (sigw (f)))))
		        (:instance expo>= (x (mana)) (n 0))))))

(local-defthmd si-expshft-norm
  (implies (and (not (specialp))
                (not (= (expa) 0)))
	   (equal (si (expshft) 13)
	          (+ (expo (a)) (bias (f)))))
  :hints (("Goal" :in-theory (enable expf expw specialp a si decode expshft* normalize-lemma bvecp dp sp hp f)
                  :use (bvecp-expa fnum-vals a-normp a-fields
		        (:instance expo-ndecode (x (opaw)) (f (f)))
		        (:instance si-bits (x (expa)) (n 13))
		        (:instance expo<= (x (expa)) (n (1- (expw (f)))))
		        (:instance expo>= (x (expa)) (n 0))))))

(defthmd si-expshft
  (implies (not (specialp))
	   (equal (si (expshft) 13)
	          (+ (expo (a)) (bias (f)))))
  :hints (("Goal" :use (si-expshft-denorm si-expshft-norm))))

(defthm nrepp-drepp
  (implies (not (specialp))
           (or (nrepp (a) (f))
	       (drepp (a) (f))))
  :rule-classes ()
  :hints (("Goal" :use (a-fields a-normp a-denormp)
                  :in-theory (enable specialp decode a))))

(defthm rationalp-abs
  (implies (rationalp x) (rationalp (abs x)))
  :rule-classes (:type-prescription :rewrite))

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

(defthm p-vals
  (member (p) '(53 24 11))
  :rule-classes ()
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable dp sp hp p prec f))))

(defthmd siga-low
  (implies (not (specialp))
           (equal (bits (siga) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable bits)
                  :use (a-pos exactp-siga p-vals
		        (:instance mod-prod (k (expt 2 (- 53 (p)))) (m (* (expt 2 (- (p) 53)) (siga))) (n 1))))))

(defthmd a-siga
  (implies (not (specialp))
           (equal (a)
	          (* (expt 2 (- (si (expshft) 13) (+ 52 (bias (f)))))
		     (siga))))
  :hints (("Goal" :in-theory (enable siga-rewrite si-expshft)
                  :use (a-pos (:instance fp-rep (x (a)))))))

(defthmd si-expshft-bounds
  (implies (not (specialp))
           (and (>= (si (expshft) 13) (- 2 (p)))
	        (< (si (expshft) 13) (1- (expt 2 (expw (f)))))))
  :hints (("Goal" :in-theory (enable p prec expw dp sp hp bias f nrepp drepp si-expshft)
                  :use (nrepp-drepp))))

(local-defthmd expq-rewrite-1
  (implies (not (specialp))
           (equal (expq)
	          (bits (+ (si (expshft) 13) (bias (f))) 11 1)))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable si p prec expw dp sp hp bias f bits-bits expq* expshft* normalize-lemma))))

(defthmd expq-rewrite
  (implies (not (specialp))
           (equal (expq)
	          (fl (/ (+ (si (expshft) 13) (bias (f))) 2))))
  :hints (("Goal" :use (fnum-vals si-expshft-bounds)
                  :in-theory (enable bits expq-rewrite-1 si p prec expw dp sp hp bias f))))

(defthm integerp-expshft
  (implies (not (specialp))
           (integerp (expshft)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable normalize-lemma expshft* expa analyze))))

(defthm integerp-si-expshft
  (implies (not (specialp))
           (integerp (si (expshft) 13)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si))))

(defthmd expq-bounds
  (implies (not (specialp))
           (and (< 0 (expq))
	        (< (expq) (- (expt 2 (expw (f))) 2))))
  :hints (("Goal" :use (fnum-vals si-expshft-bounds)
                  :in-theory (enable bits expq-rewrite p prec expw dp sp hp bias f))))
