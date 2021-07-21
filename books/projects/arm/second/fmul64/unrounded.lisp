(in-package "RTL")

(include-book "product")

(defund ea ()
  (if (= (expa) 0)
      (- 1 (1- (expt 2 10)))
    (- (expa) (1- (expt 2 10)))))

(defund eb ()
  (if (= (fscale) 1)
      (si (scale) 64)
    (if (= (expb) 0)
        (- 1 (1- (expt 2 10)))
      (- (expb) (1- (expt 2 10))))))

(in-theory (disable (ea) (eb)))

(defthmd bvecp-expa
  (bvecp (expa) 11)
  :hints (("Goal" :in-theory (enable expf dp) :use (a-fields))))

(defthmd bvecp-expb
  (bvecp (expb) 11)
  :hints (("Goal" :in-theory (enable expf dp) :use (b-fields))))

(defthmd bvecp-scale
  (bvecp (scale) 64)
  :hints (("Goal" :use (input-constraints-lemma) :in-theory (enable input-constraints))))

(defthmd scale-bounds
  (and (integerp (si (scale) 64))
       (< (si (scale) 64) (expt 2 63))
       (>= (si (scale) 64) (- (expt 2 63))))
  :hints (("Goal" :use (bvecp-scale
                        (:instance bitn-plus-bits (x (scale)) (n 63) (m 0))
			(:instance bits-bounds (x (scale)) (i 62) (j 0)))
		  :in-theory (enable bvecp si))))

(defthm integerp-ea
  (integerp (ea))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable ea bvecp) :use (bvecp-expa))))

(defthm integerp-eb
  (integerp (eb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable eb bvecp) :use (scale-bounds bvecp-expb))))

(defund a () (decode (opaz) (dp)))

(defund b () (if1 (fscale) (expt 2 (si (scale) 64)) (decode (opbz) (dp))))

(in-theory (disable (a) (b)))

(defthm a-normp-denormp
  (implies (not (specialp))
           (or (normp (opaz) (dp))
               (denormp (opaz) (dp))))
  :rule-classes ()
  :hints (("Goal" :use (member-classa a-class)
                  :in-theory (enable specialp))))

(defthm b-normp-denormp
  (implies (not (specialp))
           (or (normp (opbz) (dp))
               (denormp (opbz) (dp))))
  :rule-classes ()
  :hints (("Goal" :use (member-classb b-class)
                  :in-theory (enable specialp))))

(defthmd a-val
  (implies (not (specialp))
           (equal (abs (a))
                  (* (expt 2 (- (ea) 52))
                     (sa))))
  :hints (("Goal" :in-theory (enable decode ndecode ddecode specialp sa sb ea eb a b dp prec manf sigf)
                  :use (a-fields a-normp-denormp))))

(defthm manb-0
  (implies (= (fscale) 1)
           (equal (manb) 0))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable manb analyze input-constraints))))

(defthm expb-not-0
  (implies (= (fscale) 1)
           (equal (expb) #x3ff))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable expb analyze input-constraints))))

(defthm signb-0
  (implies (= (fscale) 1)
           (equal (signb) 0))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable signb analyze input-constraints))))

(defthmd bitp-fscale
  (bitp (fscale))
  :hints (("Goal" :use (input-constraints-lemma) :in-theory (enable input-constraints))))

(defthmd b-val
  (implies (not (specialp))
           (equal (abs (b))
                  (* (expt 2 (- (eb) 52))
                     (sb))))
  :hints (("Goal" :in-theory (enable decode ndecode ddecode specialp sa sb ea eb a b dp prec manf sigf)
                  :use (scale-bounds bitp-fscale b-fields b-normp-denormp))))

(local-defthmd abs-prod-1
  (equal (abs (* (a) (b)))
         (* (abs (a)) (abs (b)))))

(defthmd abs-prod
  (implies (not (specialp))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (+ (ea) (eb) -104))
		     (prod))))
  :hints (("Goal" :use (a-val b-val)
                  :in-theory (e/d (abs-prod-1 prod-rewrite) (abs)))))

(local-defthmd expab-bound
  (implies (not (specialp))
           (and (<= (expa) (- (expt 2 11) 2))
	        (<= (expb) (- (expt 2 11) 2))))
  :hints (("Goal" :use (a-fields b-fields bvecp-expa bvecp-expb a-normp-denormp b-normp-denormp normp denormp)
                  :in-theory (enable bvecp normp denormp dp expf prec))))

(defthmd hugepos-rewrite
  (equal (hugeposscale)
         (if (>= (eb) (expt 2 12)) 1 0))
  :hints (("Goal" :in-theory (enable hugeposscale bvecp eb)
                  :use (scale-bounds bvecp-expb))))

(defthmd hugeneg-rewrite
  (equal (hugenegscale)
         (if (< (eb) (- (expt 2 12))) 1 0))
  :hints (("Goal" :in-theory (enable hugenegscale bvecp eb)
                  :use (scale-bounds bvecp-expb))))

(defthmd expbunbiased-rewrite
  (implies (and (= (hugeposscale) 0)
                (= (hugenegscale) 0))
           (equal (si (expbunbiased) 14)
	          (eb)))
  :hints (("Goal" :in-theory (enable si bvecp expbunbiased hugeposscale hugenegscale bvecp eb)
                  :use (scale-bounds bvecp-expb (:instance si-bits (x (eb)) (n 14))))))

(defthmd expabiased-rewrite
  (equal (si (expabiased) 14)
	 (+ (ea) 1023))
  :hints (("Goal" :in-theory (enable expabiased bvecp ea)
                  :use (bvecp-expa (:instance si-bits (x (+ (ea) 1023)) (n 14))))))

(defthmd expbiased-rewrite
  (implies (and (= (hugeposscale) 0)
                (= (hugenegscale) 0))
           (equal (si (expbiased) 14)
	          (+ (ea) (eb) 1023)))
  :hints (("Goal" :in-theory (enable expbiased expbunbiased-rewrite expabiased-rewrite hugepos-rewrite hugeneg-rewrite bvecp ea)
                  :use (bvecp-expa (:instance si-bits (x (+ (ea) (eb) 1023)) (n 14))))))

(defthmd expbiased-bounds
  (implies (and (= (hugeposscale) 0)
                (= (hugenegscale) 0))
           (and (< -4096 (si (expbiased) 14))
	        (> 6144 (si (expbiased) 14))))
  :hints (("Goal" :in-theory (enable expbiased expbunbiased-rewrite expabiased-rewrite hugepos-rewrite hugeneg-rewrite bvecp ea)
                  :use (bvecp-expa (:instance si-bits (x (+ (ea) (eb) 1023)) (n 14))))))

(defthm left-right
  (implies (= (hugeposscale) 0)
           (iff (or (<= (si (expbiased) 14) 0)
	            (= (hugenegscale) 1))
		(<= (+ (ea) (eb) 1023) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expbiased-rewrite hugepos-rewrite hugeneg-rewrite bvecp ea)
                  :use (bvecp-expa))))

(defund expdeficit ()
  (bits (- 1 (si (expbiased) 14)) 13 0))

(defund rshift ()
  (let ((shift (bits (expdeficit) 5 0)))
    (if1 (logior1 (hugenegscale) (log<> (bits (expdeficit) 13 6) 0))
         (setbits shift 6 5 1 31)
         shift)))

(defund prod0 () (setbits (bits 0 106 0) 107 106 1 (prod)))

(defund rprodshft () (bits (ash (prod0) (- (rshift))) 105 0))

(defund rfrac105 () (bits (rprodshft) 104 0))

(defund rexpshft () (bits 0 12 0))

(defund rexpinc ()
  (logand1 (bitn (prod) 105)
           (log= (rshift) 1)))

(defund stkshftmask () (rightshft-loop-0 0 (rshift) (bits 0 62 0)))

(defund rstkshft ()
  (log<> (logand (prod) (ash (stkshftmask) (- 1)))
         0))

(defund rstkmask ()
  (setbits (bits 4503599627370495 106 0)
           107 106 52 (bits (stkshftmask) 54 0)))

(defund rstk ()
  (log<> (logand (prod) (bits (rstkmask) 106 1))
         0))

(defund rgrdmask ()
  (bits (logand (lognot (bits (rstkmask) 106 52))
                (bits (rstkmask) 105 51))
        54 0))

(defund rlsb ()
  (log<> (logand (bits (rgrdmask) 53 0)
                 (bits (prod) 105 52))
         0))
	 
(defund rgrd ()
  (log<> (logand (rgrdmask) (bits (prod) 105 51))
         0))

(defthmd rightshft-lemma 
  (implies (not (eql (logior1 (log<= (si (expbiased) 14) 0)
                              (hugenegscale))
		     0))
           (and (equal (expshft) (rexpshft))
	        (equal (expinc) (rexpinc))
	        (equal (frac105) (rfrac105))
	        (equal (stkshft) (rstkshft))
	        (equal (lsb) (rlsb))
	        (equal (grd) (rgrd))
	        (equal (stk) (rstk))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(expdeficit rshift prod0 rprodshft rfrac105 rexpshft rexpinc stkshftmask rstkshft rstkmask rstk rgrdmask
	                rlsb rgrd expshft expinc frac105 stkshft lsb grd stk rightshft))))

(in-theory (disable (expdeficit) (rshift) (prod0) (rprodshft) (rfrac105) (rexpshft) (rexpinc) (stkshftmask) (rstkshft)
                    (rstkmask) (rstk) (rgrdmask) (rlsb) (rgrd)))

(defund expdiff () (bits (- (si (expbiased) 14) (lzc)) 13 0))

(defund lshift ()
  (bits (if1 (log= (si (expdiff) 14) 0)
             (- (lzc) 1)
             (if1 (log> (si (expdiff) 14) 0)
                  (lzc)
		  (- (si (expbiased) 14) 1)))
	5 0))

(defund lprodshft () (bits (ash (prod) (lshift)) 105 0))

(defund lexpshft ()
  (bits (if1 (log> (si (expdiff) 14) 0)
             (si (expdiff) 14)
             0)
        12 0))

(defund ovfmask ()
  (bits (ash 9223372036854775808 (- (lshift)))
        63 0))

(defund mulovf ()
  (log<> (logand (ovfmask) (bits (prod) 105 42))
         0))

(defund sub2norm ()
  (log<> (logand (ash (ovfmask) (- 1))
                 (bits (prod) 104 42))
         0))

(defund lfrac105 ()
  (if1 (lognot1 (mulovf))
       (bits (ash (bits (lprodshft) 104 0) 1) 104 0)
       (bits (lprodshft) 104 0)))

(defund lexpinc ()
  (logior1 (mulovf)
           (logand1 (LOG= (SI (EXPDIFF) 14) 0) (sub2norm))))

(defund lstkmask ()
  (bits (ash 4503599627370495 (- (lshift))) 51 0))

(defund lstk ()
  (if1 (mulovf)
       (log<> (logand (lstkmask) (prod)) 0)
       (log<> (logand (ash (lstkmask) (- 1)) (prod)) 0)))

(defund lgrdmask () (bits (ovfmask) 63 11))

(defund lgrd ()
  (if1 (mulovf)
       (log<> (logand (lgrdmask) (prod)) 0)
       (log<> (logand (ash (lgrdmask) (- 1)) (prod)) 0)))

(defund lsbmask () (bits (ovfmask) 63 10))

(defund llsb ()
  (if1 (mulovf)
       (log<> (logand (lsbmask) (prod)) 0)
       (log<> (logand (ash (lsbmask) (- 1)) (prod)) 0)))
  
(defthmd leftshft-lemma 
  (implies (eql (logior1 (log<= (si (expbiased) 14) 0)
                         (hugenegscale))
	 	0)
           (and (equal (expshft) (lexpshft))
	        (equal (expinc) (lexpinc))
	        (equal (frac105) (lfrac105))
	        (equal (stkshft) 0)
	        (equal (lsb) (llsb))
	        (equal (grd) (lgrd))
	        (equal (stk) (lstk))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(expdiff lshift lprodshft lfrac105 ovfmask mulovf
	                sub2norm lexpshft lexpinc stkshftmask lstkmask lstk lsbmask lgrdmask llsb lgrd expshft
			expinc frac105 stkshft lsb grd stk leftshft))))

(in-theory (disable (expdiff) (lshift) (lprodshft) (lfrac105) (lexpshft) (lexpinc) (ovfmask) (mulovf)
                    (sub2norm) (lstkmask) (lstk) (lgrdmask) (lgrd) (lsbmask) (llsb)))

(defthmd expdeficit-rewrite
  (implies (and (= (hugeposscale) 0)
                (= (hugenegscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (expdeficit)
		  (- 1 (+ (ea) (eb) (1- (expt 2 10))))))
  :hints (("Goal" :in-theory (enable expdeficit expbiased-rewrite)
                  :use (expbiased-bounds))))

(defund eab ()
  (+ (expshft) (expinc) -1023))

(in-theory (disable (eab)))

(defthmd expinc-0-1
  (implies (not (specialp))
           (bitp (expinc)))
  :hints (("Goal" :cases ((eql (logior1 (log<= (si (expbiased) 14) 0) (hugenegscale)) 0))
                  :in-theory (enable rightshft-lemma leftshft-lemma lexpinc rexpinc))))  

(defthm integerp-eab
  (implies (not (specialp))
           (integerp (eab)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si lexpshft rexpshft eab)
                  :use (rightshft-lemma leftshft-lemma expinc-0-1))))

(defthmd eab-bound
  (implies (not (specialp))
           (>= (+ (eab) (1- (expt 2 10))) 0))
  :hints (("Goal" :use (expinc-0-1 leftshft-lemma rightshft-lemma)
                  :in-theory (enable lexpshft rexpshft eab))))

(local-defthmd case-1-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (expshft) 0))
  :hints (("Goal" :use (left-right rightshft-lemma)
                  :in-theory (enable rexpshft))))

(local-defthmd case-1-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (+ (eab) 1023) (expinc)))
  :hints (("Goal" :in-theory (enable case-1-1 eab))))

(local-defthmd case-1-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (hugenegscale) 1)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (member (rshift) '(62 63)))
  :hints (("Goal" :in-theory (enable bitn-bits rshift) :use ((:instance bitn-0-1 (x (expdeficit)) (n 0))))))

(defthm integerp-expbiased
  (integerp (si (expbiased) 14))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si expbiased))))

(local-defthmd case-1-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (hugenegscale) 0)
		(>= (expdeficit) 64)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (member (rshift) '(62 63)))
  :hints (("Goal" :in-theory (enable bvecp bitn-bits rshift expdeficit)
                  :use (expbiased-bounds left-right
		        (:instance bits-plus-bits (x (expdeficit)) (n 13) (p 6) (m 0))
			(:instance bits-bounds (x (expdeficit)) (i 5) (j 0))
		        (:instance bitn-0-1 (x (expdeficit)) (n 0))))))

(local-defthmd case-1-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (hugenegscale) 0)
		(< (expdeficit) 64)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (> (rshift) 0))
  :hints (("Goal" :in-theory (enable expbiased-rewrite bvecp bitn-bits rshift expdeficit)
                  :use (expbiased-bounds left-right
		        (:instance bits-plus-bits (x (expdeficit)) (n 13) (p 6) (m 0))
			(:instance bits-bounds (x (expdeficit)) (i 5) (j 0))
		        (:instance bitn-0-1 (x (expdeficit)) (n 0))))))

(local-defthmd case-1-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (hugenegscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (expdeficit) 64))
	   (equal (rshift) (expdeficit)))
  :hints (("Goal" :in-theory (enable expbiased-rewrite bvecp bitn-bits rshift expdeficit)
                  :use (expbiased-bounds left-right
		        (:instance bits-plus-bits (x (expdeficit)) (n 13) (p 6) (m 0))
			(:instance bits-bounds (x (expdeficit)) (i 5) (j 0))
			(:instance bits-plus-bitn (x (rshift)) (n 5) (m 0))))))

(defthmd rshift-bounds
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (and (> (rshift) 0) (< (rshift) 64)))
  :hints (("Goal" :in-theory (enable expdeficit-rewrite)
                  :use (case-1-3 case-1-4 case-1-5 case-1-6))))

(local-defthmd case-1-8
  (implies (and (natp shift)
                (< shift 64)
		(natp i)
		(<= i shift))
	   (equal (rightshft-loop-0 i shift (1- (expt 2 i)))
	          (1- (expt 2 shift))))
  :hints (("Goal" :in-theory (enable rightshft-loop-0)) 
          ("Subgoal *1/4" :nonlinearp t :in-theory (enable rightshft-loop-0 bvecp-bits-0 cat bvecp))))

(defthmd case-1-9
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkshftmask)
	          (1- (expt 2 (rshift)))))
  :hints (("Goal" :in-theory (enable bvecp stkshftmask)
                  :use (rshift-bounds (:instance case-1-8 (shift (rshift)) (i 0))))))

(defthm case-1-10
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (equal (expshft) (rexpshft))
	        (equal (expinc) (rexpinc))
	        (equal (frac105) (rfrac105))
	        (equal (stkshft) (rstkshft))
	        (equal (lsb) (rlsb))
	        (equal (grd) (rgrd))
	        (equal (stk) (rstk))))
  :hints (("Goal" :use (rightshft-lemma)
                  :in-theory (enable expbiased-rewrite hugeneg-rewrite))))

(defthmd case-1-11
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkshft)
	          (if (= (bits (prod) (- (rshift) 2) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable bvecp ash-rewrite bits-mod case-1-9 rstkshft)
                  :cases ((= (rshift) 0))
                  :use (rshift-bounds
		        (:instance logand-bits (x (prod)) (k 0) (n (rshift)))))))

(defthmd bvecp-prod
  (implies (not (specialp))
           (bvecp (prod) 106))
  :hints (("Goal" :use (bvecp-mana bvecp-manb)
                  :nonlinearp t
                  :in-theory (enable bvecp sa sb prod-rewrite))))

(defthmd case-1-12
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkshft)
	          (if (= (bits (prod0) (1- (rshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable bvecp prod0 cat case-1-11)
                  :cases ((= (rshift) 0))
                  :use (bvecp-prod (:instance bits-shift-up-2 (x (prod)) (k 1) (i (- (rshift) 2)))))))

(local-defthmd case-1-13
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (rprodshft)
	          (bits (prod0) (+ 105 (rshift)) (rshift))))
  :hints (("Goal" :use (rshift-bounds (:instance bits-shift-down-1 (x (prod0)) (k (rshift)) (i 105) (j 0)))
                  :in-theory (enable rprodshft ash-rewrite))))

(defthmd bvecp-prod0
  (implies (not (specialp))
           (bvecp (prod0) 107))
  :hints (("Goal" :use (bvecp-prod)
                  :nonlinearp t
                  :in-theory (enable bvecp prod0 ash-rewrite))))

(defthmd case-1-14
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (rprodshft)
	          (bits (prod0) 106 (rshift))))
  :hints (("Goal" :use (rshift-bounds bvecp-prod0
                        (:instance bits-plus-bits (x (prod0)) (n (+ 105 (rshift))) (p 107) (m (rshift))))
                  :in-theory (enable bvecp-bits-0 case-1-13))))

(defthmd case-1-15
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (frac105)
	          (if (= (rshift) 1)
		      (bits (prod0) 105 (rshift))
		    (bits (prod0) 106 (rshift)))))
  :hints (("Goal" :use (rshift-bounds bvecp-prod0)
                  :in-theory (enable rfrac105 case-1-14 bits-bits))))

(local-defthmd case-1-16
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (> (rshift) 54))
  :hints (("Goal" :use (case-1-3 case-1-4 case-1-6))))

(local-defthmd case-1-17
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (equal (bits (frac105) 104 52) 0))
  :hints (("Goal" :use (case-1-16) :in-theory (enable case-1-15 bits-bits))))

(local-defthmd case-1-18
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (equal (bits (frac105) 51 0)
	          (bits (prod0) 106 (rshift))))
  :hints (("Goal" :use (case-1-16) :in-theory (enable case-1-15 bits-bits))))

(local-defthmd case-1-19
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (equal (+ (eab) 1023) 0))
  :hints (("Goal" :use (case-1-16) :in-theory (enable rexpinc case-1-2))))

(defthmd ab-non-zero
  (implies (not (specialp))
           (not (= (* (a) (b)) 0)))
  :hints (("Goal" :in-theory (enable a b decode nrepp drepp normp denormp ddecode ndecode)
                  :use (a-normp-denormp b-normp-denormp))))

(defthmd prod-non-zero
  (implies (not (specialp))
           (not (= (prod) 0)))
  :hints (("Goal" :use (ab-non-zero abs-prod))))

(defthmd prod0-non-zero
  (implies (not (specialp))
           (not (= (prod0) 0)))
  :hints (("Goal" :use (bvecp-prod prod-non-zero)
                  :in-theory (enable bvecp prod0 ash-rewrite cat))))

(defthmd bvecp-frac105
  (implies (not (specialp))
           (bvecp (frac105) 105))
  :hints (("Goal" :in-theory (enable lfrac105 rfrac105) :use (rightshft-lemma leftshft-lemma))))

(local-defthm case-1-20
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (not (and (= (bits (frac105) 51 0) 0)
	             (= (stkshft) 0))))
  :rule-classes ()
  :hints (("Goal" :use (bvecp-prod0 prod0-non-zero case-1-18 rshift-bounds
                        (:instance bits-plus-bits (x (prod0)) (n 106) (p (rshift)) (m 0)))
                  :in-theory (enable case-1-12))))

(defthmd ab-hugeneg-1
  (implies (and (not (specialp))
                (= (hugenegscale) 1))
           (< (abs (b)) (expt 2 -4096)))
  :hints (("Goal" :use (sb eb expab-bound bvecp-expb b-val)
                  :in-theory (enable hugeneg-rewrite)
		  :nonlinearp t)))

(defthmd ab-hugeneg-2
  (implies (not (specialp))
           (<= (abs (a)) (lpn (dp))))
  :hints (("Goal" :use (expab-bound bvecp-expa bvecp-mana a-val)
                  :in-theory (enable ea sa lpn dp bias)
		  :nonlinearp t)))

(defthmd ab-hugeneg-3
  (implies (and (not (specialp))
                (= (hugenegscale) 1))
           (< (abs (* (a) (b))) (expt 2 (- -52 1023))))
  :hints (("Goal" :use (abs-prod-1 ab-hugeneg-1 ab-hugeneg-2)
                  :in-theory (enable lpn bias dp)
		  :nonlinearp t)))

(local-defthm case-1-21
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (<= (+ (ea) (eb))
	       (- -54 (1- (expt 2 10)))))
  :rule-classes ()
  :hints (("Goal" :cases ((and (= (expa) 0) (= (expb) 0))))
          ("Subgoal 2" :in-theory (enable expdeficit-rewrite))
          ("Subgoal 1" :in-theory (enable ea eb))))

(local-defthm case-1-22
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
	   (and (integerp (+ (ea) (eb) -104))
	        (integerp (- -158 (1- (expt 2 10))))
                (<= (+ (ea) (eb) -104)
	            (- -158 (1- (expt 2 10))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-21) :nonlinearp t)))

(local-defthmd case-1-23
  (implies (and (integerp x) (integerp y) (<= x y))
           (<= (expt 2 x) (expt 2 y))))

(local-defthm case-1-24
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (<= (expt 2 (+ (ea) (eb) -104))
	       (expt 2 (- -158 (1- (expt 2 10))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-22
                        (:instance case-1-23 (x (+ (ea) (eb) -104)) (y (- -158 (1- (expt 2 10))))))
		  :nonlinearp t)))

(local-defthm case-1-25
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (< (abs (* (a) (b)))
	      (expt 2 (- -52 (1- (expt 2 10))))))
  :rule-classes ()
  :hints (("Goal" :use (ab-hugeneg-3 case-1-24 bvecp-prod)
                  :in-theory (e/d (abs-prod bvecp) (abs))
		  :nonlinearp t)))

(local-defthm case-1-26
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(or (= (hugenegscale) 1)
		    (> (expdeficit) 54)))
           (and (equal (+ (eab) (1- (expt 2 10))) 0)
	        (< (* (expt 2 (- -52 (1- (expt 2 10))))
		      (bits (frac105) 104 52))
		   (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))
		(not (and (= (bits (frac105) 51 0) 0)
	                  (= (stkshft) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (ab-non-zero case-1-25 case-1-19 case-1-17 case-1-20))))

(local-defthm case-1-27
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54))
           (and (<= (rshift) 54)
	        (= (rshift) (- 1 (+ (ea) (eb) (1- (expt 2 10)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-6)
                  :in-theory (enable expdeficit-rewrite))))

(local-defthm case-1-28
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (+ (eab) (1- (expt 2 10)))
	          1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rexpinc case-1-2))))

(local-defthm case-1-29
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (+ (ea) (eb) (1- (expt 2 10)))
	          0))
  :rule-classes ()
  :hints (("Goal" :use (case-1-27))))

(local-defthmd case-1-30
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (eab)
	          (+ (ea) (eb) 1)))
  :hints (("Goal" :use (case-1-29 case-1-28))))

(local-defthmd case-1-31
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (rprodshft)
	          (prod)))
  :hints (("Goal" :use (bvecp-prod)
                  :in-theory (enable rprodshft prod0 cat bvecp ash-rewrite))))

(local-defthmd case-1-32
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (frac105)
	          (bits (prod) 104 0)))
  :hints (("Goal" :use (bvecp-prod
                        (:instance bits-shift-up-1 (x (prod)) (k 1) (i 105) (j 1)))
                  :in-theory (enable case-1-15 prod0 cat bvecp ash-rewrite))))

(local-defthmd case-1-33
  (implies (and (not (specialp)) (= (bitn (prod) 105) 1))
           (equal (prod) (+ (expt 2 105) (bits (prod) 104 0))))
  :hints (("Goal" :use (bvecp-prod (:instance bitn-plus-bits (x (prod)) (n 105) (m 0))))))

(local-defthmd case-1-34
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (+ (ea) (eb) -104))
		     (+ (expt 2 105) (frac105)))))
  :hints (("Goal" :use (case-1-33) :in-theory (e/d (case-1-30 case-1-32 abs-prod) (abs)))))

(local-defthmd case-1-35
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (* (expt 2 (+ (ea) (eb) -104))
		     (+ (expt 2 105) (frac105)))
		  (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (enable case-1-30))))

(local-defthmd case-1-36
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :use (case-1-34 case-1-35))))

(local-defthmd case-1-37
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (rshift) 1))
           (equal (stkshft) 0))
  :hints (("Goal" :in-theory (enable case-1-12 prod0 ash-rewrite cat bitn-bits)
                  :use (bvecp-prod
		        (:instance bitn-shift-up (x (prod)) (k 1) (n -1))))))

(local-defthm case-1-38
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (and (equal (+ (eab) (1- (expt 2 10))) 1)
	        (equal (stkshft) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-36 case-1-28 case-1-37))))

(local-defthmd case-1-39
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (+ (eab) 1023) 0))
  :hints (("Goal" :in-theory (enable rexpinc case-1-2))))

(local-defthmd case-1-40
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (+ (ea) (eb) -105))
		     (prod0))))
  :hints (("Goal" :in-theory (e/d (abs-prod prod0 ash-rewrite bvecp cat) (abs))
                  :use (bvecp-prod))))

(local-defthmd case-1-41
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (* (expt 2 (+ (ea) (eb) -105))
		     (prod0))
	          (* (expt 2 (+ (ea) (eb) -105))
		     (+ (* (expt 2 (+ (rshift) 52))
		           (bits (prod0) 106 (+ (rshift) 52)))
		        (bits (prod0) (+ (rshift) 51) 0)))))
  :hints (("Goal" :use (bvecp-prod0 case-1-27
		        (:instance bits-plus-bits (x (prod0)) (n 106) (p (+ (rshift) 52)) (m 0))))))

(local-defthmd case-1-42
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (* (expt 2 (+ (ea) (eb) -105))
		     (prod0))
	          (* (expt 2 (+ (ea) (eb) -105 (rshift) 52))
		     (+ (bits (prod0) 106 (+ (rshift) 52))
		        (* (expt 2 (- (+ (rshift) 52)))
			   (bits (prod0) (+ (rshift) 51) 0))))))
  :hints (("Goal" :use (bvecp-prod0 case-1-41))))

(local-defthmd case-1-43
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (+ (ea) (eb) -105 (rshift) 52)
	          (- -52 (1- (expt 2 10)))))
  :hints (("Goal" :use (case-1-27))))

(local-defthmd case-1-44
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -52 (1- (expt 2 10))))
		     (+ (bits (prod0) 106 (+ (rshift) 52))
		        (* (expt 2 (- (+ (rshift) 52)))
			   (bits (prod0) (+ (rshift) 51) 0))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (case-1-40 case-1-42 case-1-43))))

(local-defthmd case-1-45
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(> (rshift) 1))
           (equal (bits (frac105) 104 52)
	          (bits (prod0) 106 (+ (rshift) 52))))
  :hints (("Goal" :in-theory (enable case-1-15)
                  :use (case-1-27))))

(local-defthmd case-1-46
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 0)
		(= (rshift) 1))
           (equal (bitn (prod0) 106) 0))
  :hints (("Goal" :in-theory (enable bvecp prod0 ash-rewrite cat bitn-bits)
                  :use (bvecp-prod (:instance bitn-shift-up (x (prod)) (k 1) (n 105))))))

(local-defthmd case-1-47
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 0)
		(= (rshift) 1))
           (equal (bits (frac105) 104 52)
	          (bits (prod0) 106 (+ (rshift) 52))))
  :hints (("Goal" :in-theory (enable case-1-46 case-1-15)
                  :use (case-1-27 (:instance bitn-plus-bits (x (prod0)) (n 106) (m (+ (rshift) 52)))))))

(local-defthmd case-1-48
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -52 (1- (expt 2 10))))
		     (+ (bits (frac105) 104 52)
		        (* (expt 2 (- (+ (rshift) 52)))
			   (bits (prod0) (+ (rshift) 51) 0))))))
  :hints (("Goal" :use (rshift-bounds case-1-47 case-1-45 case-1-44))))

(local-defthmd case-1-49
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (frac105) 104 52))
		    (abs (* (a) (b))))
		(< (abs (* (a) (b)))
	           (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))))
  :hints (("Goal" :use ((:instance bits-bounds (x (prod0)) (i (+ (rshift) 51)) (j 0)))
		  :in-theory (e/d (case-1-48) (abs))
		  :nonlinearp t)))

(local-defthmd case-1-50
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (iff (equal (abs (* (a) (b)))
	               (* (expt 2 (- -52 (1- (expt 2 10))))
		          (bits (frac105) 104 52)))
		(equal (bits (prod0) (+ (rshift) 51) 0)
		       0)))
  :hints (("Goal" :in-theory (e/d (case-1-48) (abs)))))

(local-defthmd case-1-51
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (iff (equal (bits (prod0) (+ (rshift) 51) 0)
		       0)
		(and (equal (bits (prod0) (+ (rshift) 51) (rshift))
		            0)
	             (equal (bits (prod0) (1- (rshift)) 0)
		            0))))
  :hints (("Goal" :use ((:instance bits-plus-bits (x (prod0)) (n (+ (rshift) 51)) (p (rshift)) (m 0))))))

(local-defthmd case-1-52
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (bits (prod0) (+ (rshift) 51) (rshift))
		  (bits (frac105) 51 0)))
  :hints (("Goal" :in-theory (enable case-1-15 bits-bits) :use (case-1-27))))

(local-defthmd case-1-53
  (implies (and (not (specialp))
                (= (hugenegscale) 0)
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (iff (equal (bits (prod0) (+ (rshift) 51) 0)
		       0)
		(and (equal (bits (frac105) 51 0)
		            0)
	             (equal (stkshft)
		            0))))
  :hints (("Goal" :use (case-1-51 case-1-52 case-1-12))))

(local-defthm case-1-a
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkshft) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :rule-classes ()
  :hints (("Goal" :use (rshift-bounds case-1-26 case-1-38 case-1-39))))

(local-defthm case-1-b
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (eab) (1- (expt 2 10))) 0))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (frac105) 104 52))
		    (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))
		(iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
		           (bits (frac105) 104 52))
		        (abs (* (a) (b))))
	             (and (equal (bits (frac105) 51 0)
		            0)
	             (equal (stkshft)
		            0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
                  :use (rshift-bounds case-1-26 case-1-38 case-1-39 case-1-49 case-1-50 case-1-53
                        (:instance bitn-0-1 (x (prod)) (n 105))))))

(defthm expa-expb-0
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (not (and (= (expa) 0) (= (expb) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ea eb))))

(defthm natp-expa
  (natp (expa))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (bvecp-expa))))

(defthm natp-expb
  (natp (expb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (bvecp-expb))))

(defthmd expa-0-mana
  (implies (and (not (specialp))
                (= (expa) 0))
           (not (= (mana) 0)))
  :hints (("Goal" :use (a-fields a-class bvecp-expa a-normp-denormp normp denormp)
                  :in-theory (enable manf sigf specialp bvecp normp denormp dp expf prec))))

(defthmd expb-0-manb
  (implies (and (not (specialp))
                (= (expb) 0))
           (not (= (manb) 0)))
  :hints (("Goal" :use (b-fields b-class bvecp-expb b-normp-denormp normp denormp)
                  :in-theory (enable manf sigf specialp bvecp normp denormp dp expf prec))))

(defthmd clz-mana-pos
  (implies (and (not (specialp)) (= (expa) 0))
           (not (zp (clz53 (mana)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-mana expa-0-mana
                        (:instance expo<= (x (mana)) (n 51))
                        (:instance clz-expo (s (mana)))))))

(defthmd clz-manb-pos
  (implies (and (not (specialp)) (= (expb) 0))
           (not (zp (clz53 (manb)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-manb expb-0-manb
                        (:instance expo<= (x (manb)) (n 51))
                        (:instance clz-expo (s (manb)))))))

(defthmd clz-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (lzc)
	          (if (= (expa) 0)
		      (clz53 (mana))
		    (if (= (expb) 0)
		        (clz53 (manb))
		      0))))
  :hints (("Goal" :use (clz-mana-pos clz-manb-pos expab-bound) :in-theory (enable ea eb lzc))))

(defthmd expo-sa
  (implies (not (specialp))
           (equal (expo (sa))
	          (if (= (expa) 0)
		      (expo (mana))
		    52)))
  :hints (("Goal" :in-theory (enable bvecp sa)
                  :use (bvecp-mana
		        (:instance expo-unique (x (sa)) (n 52))))))

(defthmd expo-sb
  (implies (not (specialp))
           (equal (expo (sb))
	          (if (= (expb) 0)
		      (expo (manb))
		    52)))
  :hints (("Goal" :in-theory (enable bvecp sb)
                  :use (bvecp-manb
		        (:instance expo-unique (x (sb)) (n 52))))))

(defthmd expo-sa-sb
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (+ (expo (sa)) (expo (sb)))
	          (- 104 (lzc))))
  :hints (("Goal" :in-theory (enable clz-rewrite bvecp clz-expo expo-sa expo-sb)
                  :use (expa-expb-0 bvecp-mana bvecp-manb expa-0-mana expb-0-manb))))

(defthmd expo-product
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (member (expo (prod))
	           (list (- 104 (lzc)) (- 105 (lzc)))))
  :hints (("Goal" :in-theory (enable sa sb prod-rewrite)
                  :use (bvecp-mana bvecp-manb expo-sa-sb (:instance expo-prod (x (sa)) (y (sb)))))))

(defthm case-2-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (equal (expshft) (lexpshft))
	        (equal (expinc) (lexpinc))
	        (equal (frac105) (lfrac105))
	        (equal (stkshft) 0)
	        (equal (lsb) (llsb))
	        (equal (grd) (lgrd))
	        (equal (stk) (lstk))))
  :hints (("Goal" :use (leftshft-lemma left-right)
                  :in-theory (enable expbiased-rewrite hugeneg-rewrite))))

(defthmd clz-bounds
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (natp (lzc))
	        (<= (lzc) 52)))
  :hints (("Goal" :in-theory (enable bvecp clz-expo clz-rewrite)
                  :use (expa-0-mana expb-0-manb bvecp-mana bvecp-manb
		        (:instance expo<= (x (mana)) (n 52))
		        (:instance expo<= (x (manb)) (n 52))
		        (:instance expo>= (x (mana)) (n 0))
		        (:instance expo>= (x (manb)) (n 0))))))

(local-defthmd case-2-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (si (expdiff) 14)
                  (- (si (expbiased) 14)
		     (lzc))))
  :hints (("Goal" :in-theory (enable expdiff)
                  :use (left-right expbiased-bounds clz-bounds
		        (:instance si-bits (x (- (si (expbiased) 14) (lzc))) (n 14))))))

(defthmd expdiff-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (si (expdiff) 14)
                  (- (+ (ea) (eb) 1023)
		     (lzc))))
  :hints (("Goal" :in-theory (enable case-2-3 expbiased-rewrite)
                  :use (left-right))))

(in-theory (disable ACL2::|(mod (+ 1 x) y)|))

(defthmd expdiff-bounds
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
          (and (integerp (si (expdiff) 14))
	       (< -4096 (si (expdiff) 14))
	       (> 6196 (si (expdiff) 14))))
  :hints (("Goal" :in-theory (enable expdiff)
                  :use (left-right expbiased-bounds clz-bounds
		        (:instance si-bits (x (- (si (expbiased) 14) (lzc))) (n 14))))))

(local-defthmd case-2-9
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (eab)
	          (+ (ea) (eb) (- (lzc)) (expinc))))
  :hints (("Goal" :in-theory (enable expbiased-rewrite eab case-2-3 case-2-rewrite lexpshft bvecp)
                  :use (expdiff-bounds left-right))))

(local-defthmd case-2-10
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (> (+ (eab) (1- (expt 2 10)))
	      0))
  :hints (("Goal" :in-theory (enable case-2-9)
                  :use (expinc-0-1))))

(defthmd case-2-11
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lshift) (lzc)))
  :hints (("Goal" :in-theory (enable expdiff-rewrite bvecp lshift)
                  :use (clz-bounds))))

(local-defthmd case-2-12
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (< (* (expt 2 (lzc)) (prod))
	      (expt 2 106)))
  :hints (("Goal" :in-theory (enable bvecp lprodshft)
                  :use (bvecp-prod clz-bounds expo-product (:instance expo>= (x (prod)) (n (- 106 (lzc)))))
		  :nonlinearp t)))

(defthmd case-2-13
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lprodshft)
	          (* (expt 2 (lzc))
		     (prod))))
  :hints (("Goal" :in-theory (enable bvecp lprodshft case-2-11 ash-rewrite)
                  :use (bvecp-prod clz-bounds case-2-12))))

(local-defthmd case-2-14
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (member (expo (lprodshft)) '(104 105)))
  :hints (("Goal" :in-theory (enable bvecp case-2-13)
                  :use (expo-product bvecp-prod clz-bounds
		        (:instance expo-shift (x (prod)) (n (lzc)))))))

(local-defthmd case-2-15
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (ovfmask)
	          (expt 2 (- 63 (lzc)))))
  :hints (("Goal" :in-theory (enable bvecp ovfmask ash-rewrite case-2-11)
                  :use (clz-bounds))))

(local-defthmd case-2-16
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (expinc)
	          (bitn (prod) (- 105 (lzc)))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite bitn-bits case-2-15 mulovf lexpinc)
                  :use (clz-bounds
		        (:instance bitn-0-1 (x (prod)) (n (- 105 (lzc))))
		        (:instance logand-bit (x (bits (prod) 105 42)) (n (- 63 (lzc))))))))

(defthmd case-2-17
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (expinc)
	          (bitn (lprodshft) 105)))
  :hints (("Goal" :in-theory (enable case-2-13 case-2-16)
                  :use (clz-bounds bvecp-prod
		        (:instance bitn-shift-up (x (prod)) (k (lzc)) (n (- 105 (lzc))))))))

(local-defthmd case-2-18
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (expo (lprodshft)) 104))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (case-2-17 case-2-14
		        (:instance bitn-plus-bits (x (lprodshft)) (n 105) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))
			(:instance bits-bounds (x (lprodshft)) (i 104) (j 0))))))

(local-defthmd case-2-19
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (expinc)
	          (mulovf)))
  :hints (("Goal" :in-theory (enable expdiff-rewrite lexpinc))))

(local-defthmd case-2-20
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (frac105)
	          (bits (* 2 (lprodshft)) 104 0)))
  :hints (("Goal" :in-theory (enable ash-rewrite case-2-18 bvecp lfrac105)
                  :use (case-2-19 (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd case-2-21
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (frac105)
	          (* 2 (bits (lprodshft) 103 0))))
  :hints (("Goal" :in-theory (enable case-2-20)
                  :use (case-2-19 (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))))))

(local-defthmd case-2-22
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (lprodshft)
	          (+ (expt 2 104) (bits (lprodshft) 103 0))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (case-2-18
		        (:instance bitn-0-1 (x (lprodshft)) (n 104))
		        (:instance bitn-plus-bits (x (lprodshft)) (n 104) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))			
			(:instance bits-bounds (x (lprodshft)) (i 103) (j 0))))))

(local-defthmd case-2-23
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (lzc)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (abs-prod case-2-13) (abs)))))

(local-defthmd case-2-24
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (lzc)))
		     (+ (expt 2 104) (bits (lprodshft) 103 0)))))
  :hints (("Goal" :use (case-2-22)
                  :in-theory (e/d (case-2-23) (abs)))))

(local-defthmd case-2-25
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb)) (lzc)))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-24 case-2-21) (abs)))))

(local-defthmd case-2-26
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-9 case-2-25) (abs)))))

(local-defthmd case-2-27
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (expo (lprodshft)) 105))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (case-2-17 case-2-14
		        (:instance bitn-plus-bits (x (lprodshft)) (n 105) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))
			(:instance bits-bounds (x (lprodshft)) (i 104) (j 0))))))

(defthmd case-2-28
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (frac105)
	          (bits (lprodshft) 104 0)))
  :hints (("Goal" :in-theory (enable ash-rewrite case-2-27 bvecp lfrac105)
                  :use (case-2-19 (:instance expo-upper-bound (x (lprodshft)))))))

(defthmd case-2-29
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (lprodshft)
	          (+ (expt 2 105) (bits (lprodshft) 104 0))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (case-2-27
		        (:instance bitn-0-1 (x (lprodshft)) (n 105))
		        (:instance bitn-plus-bits (x (lprodshft)) (n 105) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))			
			(:instance bits-bounds (x (lprodshft)) (i 104) (j 0))))))

(local-defthmd case-2-30
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (lzc)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (abs-prod case-2-13) (abs)))))

(local-defthmd case-2-31
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (lzc)))
		     (+ (expt 2 105) (bits (lprodshft) 104 0)))))
  :hints (("Goal" :use (case-2-29)
                  :in-theory (e/d (case-2-30) (abs)))))

(local-defthmd case-2-32
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) 1) (lzc)))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-31 case-2-28) (abs)))))

(local-defthmd case-2-33
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-9 case-2-32) (abs)))))

(local-defthmd case-2-34
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :use (case-2-26 case-2-33 expinc-0-1))))

(local-defthmd case-2-35
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lshift) (1- (lzc))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite bvecp lshift)
                  :use (clz-bounds))))

(local-defthmd case-2-36
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (< (* (expt 2 (1- (lzc))) (prod))
	      (expt 2 105)))
  :hints (("Goal" :in-theory (enable bvecp lprodshft)
                  :use (bvecp-prod clz-bounds expo-product (:instance expo>= (x (prod)) (n (- 106 (lzc)))))
		  :nonlinearp t)))

(defthmd case-2-37
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lprodshft)
	          (* (expt 2 (1- (lzc)))
		     (prod))))
  :hints (("Goal" :in-theory (enable bvecp lprodshft case-2-35 ash-rewrite)
                  :use (bvecp-prod clz-bounds case-2-36))))

(local-defthmd case-2-38
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (member (expo (lprodshft)) '(104 103)))
  :hints (("Goal" :in-theory (enable bvecp case-2-37)
                  :use (expo-product bvecp-prod clz-bounds
		        (:instance expo-shift (x (prod)) (n (1- (lzc))))))))

(local-defthmd case-2-39
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (ovfmask)
	          (expt 2 (- 64 (lzc)))))
  :hints (("Goal" :in-theory (enable bvecp ovfmask ash-rewrite case-2-35)
                  :use (clz-bounds))))

(local-defthmd case-2-40
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (mulovf)
	          (bitn (prod) (- 106 (lzc)))))
  :hints (("Goal" :in-theory (enable bitn-bits case-2-39 mulovf lexpinc)
                  :use (clz-bounds
		        (:instance bitn-0-1 (x (prod)) (n (- 106 (lzc))))
		        (:instance logand-bit (x (bits (prod) 105 42)) (n (- 64 (lzc))))))))

(local-defthmd case-2-41
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (< (prod) (expt 2 (- 106 (lzc)))))
  :hints (("Goal" :in-theory (enable bvecp) :nonlinearp t
                  :use (clz-bounds expo-product
		        (:instance expo>= (x (prod)) (n (- 106 (lzc))))))))

(local-defthmd case-2-42
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (mulovf) 0))
  :hints (("Goal" :in-theory (enable bvecp case-2-40)
                  :use (clz-bounds case-2-41 bvecp-prod
		        (:instance bitn-plus-bits (x (prod)) (n (- 106 (lzc))) (m 0))
		        (:instance bits-bounds (x (prod)) (i (- 105 (lzc))) (j 0))
		        (:instance bitn-0-1 (x (prod)) (n (- 106 (lzc))))
		        (:instance expo>= (x (prod)) (n (- 106 (lzc))))))))

(local-defthmd case-2-43
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lexpinc)
	          (bitn (prod) (- 105 (lzc)))))
  :hints (("Goal" :in-theory (enable expdiff-rewrite bitn-bits ash-rewrite sub2norm case-2-39 case-2-42 lexpinc)
                  :use (clz-bounds
		        (:instance bitn-0-1 (x (prod)) (n (- 104 (lzc))))
		        (:instance logand-bit (x (bits (prod) 104 42)) (n (- 63 (lzc))))))))

(defthmd case-2-44
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (expinc)
	          (bitn (lprodshft) 104)))
  :hints (("Goal" :in-theory (enable case-2-37 case-2-43)
                  :use (clz-bounds bvecp-prod
		        (:instance bitn-shift-up (x (prod)) (k (1- (lzc))) (n (- 105 (lzc))))))))

(local-defthmd case-2-45
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -102 (expt 2 10)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (case-2-37 abs-prod) (abs))
                  :use (clz-bounds bvecp-prod))))

(defthmd case-2-46
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (frac105)
	          (* 2 (bits (lprodshft) 103 0))))
  :hints (("Goal" :in-theory (enable case-2-42 ash-rewrite bvecp lfrac105)
                  :use (case-2-38
		        (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))
		        (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd case-2-47
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (eab)
	          (+ -1023 (expinc))))
  :hints (("Goal" :in-theory (enable bvecp eab lexpshft expdiff-rewrite)
                  :use (expdiff-bounds))))

(local-defthmd case-2-48
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (expo (lprodshft)) 104))
  :hints (("Goal" :in-theory (enable case-2-44 bvecp)
                  :use (case-2-38 
		        (:instance bitn-plus-bits (x (lprodshft)) (n 104) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))
			(:instance bits-bounds (x (lprodshft)) (i 103) (j 0))))))

(defthmd case-2-49
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
           (equal (lprodshft)
	          (+ (expt 2 104) (bits (lprodshft) 103 0))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (case-2-48
		        (:instance bitn-0-1 (x (lprodshft)) (n 104))
		        (:instance bitn-plus-bits (x (lprodshft)) (n 104) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))			
			(:instance bits-bounds (x (lprodshft)) (i 103) (j 0))))))

(local-defthmd case-2-50
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 1))
	   (and (= (eab) -1022)
                (equal (abs (* (a) (b)))
    	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :hints (("Goal" :in-theory (e/d (case-2-45 case-2-46 case-2-47) (abs))
                  :use (case-2-49))))

(local-defthmd case-2-51
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (expo (lprodshft)) 103))
  :hints (("Goal" :in-theory (enable case-2-44 bvecp)
                  :use (case-2-38 
		        (:instance bitn-plus-bits (x (lprodshft)) (n 104) (m 0))
			(:instance expo-upper-bound (x (lprodshft)))
			(:instance expo-lower-bound (x (lprodshft)))
			(:instance bits-bounds (x (lprodshft)) (i 103) (j 0))))))

(local-defthmd case-2-52
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (frac105)
	          (* 2 (lprodshft))))
  :hints (("Goal" :in-theory (enable case-2-46 bvecp lfrac105)
                  :use (case-2-51
		        (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd case-2-53
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -103 (expt 2 10)))
		     (frac105))))
  :hints (("Goal" :in-theory (e/d (case-2-45 case-2-52) (abs)))))

(local-defthmd case-2-54
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -51 (expt 2 10)))
		     (+ (bits (frac105) 104 52)
		        (* (expt 2 -52) (bits (frac105) 51 0))))))
  :hints (("Goal" :in-theory (e/d (case-2-53) (abs))
                  :use (bvecp-frac105
		        (:instance bits-plus-bits (x (frac105)) (n 104) (p 52) (m 0))))))

(local-defthmd case-2-55
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (lzc))
		(= (expinc) 0))
	   (and (= (eab) -1023)
                (<=  (* (expt 2 (- -51 (expt 2 10)))
		        (bits (frac105) 104 52))
		     (abs (* (a) (b))))
		(< (abs (* (a) (b)))
	           (* (expt 2 (- -51 (expt 2 10)))
		      (1+ (bits (frac105) 104 52))))
		(iff (= (* (expt 2 (- -51 (expt 2 10)))
		           (bits (frac105) 104 52))
		        (abs (* (a) (b))))
		     (= (bits (frac105) 51 0)
		        0))))
  :hints (("Goal" :in-theory (e/d (case-2-47 case-2-54) (abs))
                  :use (:instance bits-bounds (x (frac105)) (i 51) (j 0))
		  :nonlinearp t)))

(local-defthmd case-2-56
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lshift)
	          (bits (+ (ea) (eb) 1022) 5 0)))
  :hints (("Goal" :use (left-right)
                  :in-theory (enable expdiff-rewrite expbiased-rewrite bits-bits lshift))))

(local-defthmd case-2-57
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lshift)
	          (mod (+ (ea) (eb) 1022) 64)))
  :hints (("Goal" :in-theory (enable case-2-56 bits-mod))))

(local-defthmd case-2-62
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lshift)
	          (+ (ea) (eb) 1022)))
  :hints (("Goal" :in-theory (enable case-2-57)
                  :use (clz-bounds))))

(defthmd case-2-63
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (< (prod) (expt 2 (- 106 (lzc)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (clz-bounds bvecp-prod expo-product (:instance expo>= (x (prod)) (n (- 106 (lzc))))))))

(defthmd lshift-bound
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (<= (lshift) (- (lzc) 2)))
  :hints (("Goal" :in-theory (enable case-2-62)
                  :use (clz-bounds))))

(local-defthmd hack-1
  (implies (and (integerp a)
		(integerp b)
		(integerp c)
		(rationalp x)
		(<= a b)
		(< x (expt 2 c)))
	   (< (* (expt 2 a) x) (expt 2 (+ b c))))
  :hints (("Goal" :nonlinearp t)))

(defthmd case-2-65
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (< (* (expt 2 (lshift)) (prod))
	      (expt 2 104)))
  :hints (("Goal" :nonlinearp t
                  :use (case-2-63 lshift-bound (:instance hack-1 (a (lshift)) (b (- (lzc) 2)) (c (- 106 (lzc))) (x (prod)))))))

(defthmd case-2-66
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (lprodshft)
	          (* (prod) (expt 2 (lshift)))))
  :hints (("Goal" :in-theory (enable lprodshft ash-rewrite bvecp)
                  :use (clz-bounds bvecp-prod case-2-65))))

(local-defthmd case-2-67
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (ovfmask)
	          (expt 2 (- 63 (lshift)))))
  :hints (("Goal" :in-theory (enable bvecp ovfmask ash-rewrite)
                  :use (lshift-bound clz-bounds))))

(defthmd case-2-68
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (mulovf)
	          (bitn (prod) (- 105 (lshift)))))
  :hints (("Goal" :in-theory (enable bitn-bits case-2-67 mulovf lexpinc)
                  :use (clz-bounds lshift-bound
		        (:instance bitn-0-1 (x (prod)) (n (- 105 (lshift))))
		        (:instance logand-bit (x (bits (prod) 105 42)) (n (- 63 (lshift))))))))

(local-defthmd case-2-69
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (< (expt 2 (- 106 (lzc)))
	      (expt 2 (- 105 (lshift)))))
  :hints (("Goal" :nonlinearp t
                  :use (clz-bounds lshift-bound))))

(defthmd case-2-70
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (< (prod) (expt 2 (- 105 (lshift)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (clz-bounds case-2-63 case-2-69))))

(defthmd case-2-71
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (mulovf) 0))
  :hints (("Goal" :in-theory (enable case-2-68 bvecp)
                  :use (case-2-70 bvecp-prod))))

(defthmd case-2-72
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (frac105)
	          (* 2 (lprodshft))))
  :hints (("Goal" :in-theory (enable case-2-71 case-2-66 ash-rewrite bvecp lfrac105)
                  :use (case-2-65 bvecp-prod
		        (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))))))

(local-defthmd case-2-73
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -102 (expt 2 10)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (case-2-66 case-2-62 abs-prod) (abs))
                  :use (clz-bounds bvecp-prod))))

(local-defthmd case-2-74
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -103 (expt 2 10)))
		     (frac105))))
  :hints (("Goal" :in-theory (e/d (case-2-73 case-2-72) (abs)))))

(local-defthmd case-2-75
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -51 (expt 2 10)))
		     (+ (bits (frac105) 104 52)
		        (* (expt 2 -52) (bits (frac105) 51 0))))))
  :hints (("Goal" :in-theory (e/d (case-2-74) (abs))
                  :use (bvecp-frac105
		        (:instance bits-plus-bits (x (frac105)) (n 104) (p 52) (m 0))))))

(local-defthmd case-2-76
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
           (equal (eab) -1023))
  :hints (("Goal" :in-theory (enable lexpinc bvecp eab case-2-71 expdiff-rewrite lexpshft))))

(local-defthmd case-2-77
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (lzc)))
	   (and (= (eab) -1023)
                (<=  (* (expt 2 (- -51 (expt 2 10)))
		        (bits (frac105) 104 52))
		     (abs (* (a) (b))))
		(< (abs (* (a) (b)))
	           (* (expt 2 (- -51 (expt 2 10)))
		      (1+ (bits (frac105) 104 52))))
		(iff (= (* (expt 2 (- -51 (expt 2 10)))
		           (bits (frac105) 104 52))
		        (abs (* (a) (b))))
		     (= (bits (frac105) 51 0)
		        0))))
  :hints (("Goal" :in-theory (e/d (case-2-76 case-2-75) (abs))
                  :use (:instance bits-bounds (x (frac105)) (i 51) (j 0))
		  :nonlinearp t)))

(local-defthm case-2-a
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkshft) 0)
		(equal (abs (* (a) (b)))
   	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-2-10 case-2-34 case-2-50 case-2-55 case-2-77))))

(local-defthm case-2-b
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (eab) (1- (expt 2 10))) 0))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (frac105) 104 52))
		    (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))
		(iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
		           (bits (frac105) 104 52))
		        (abs (* (a) (b))))
	             (and (equal (bits (frac105) 51 0)
		          0)
	             (equal (stkshft)
		            0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
                  :use (case-2-10 case-2-34 case-2-50 case-2-55 case-2-77))))

(defthmd unround-a
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkshft) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :hints (("Goal" :use (case-1-a case-2-a))))

(defthm unround-b
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
		(= (+ (eab) (1- (expt 2 10))) 0))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (frac105) 104 52))
		    (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))
		(iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
		           (bits (frac105) 104 52))
		        (abs (* (a) (b))))
	             (and (equal (bits (frac105) 51 0)
		            0)
	                  (equal (stkshft)
		                 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
           :use (case-1-b case-2-b))))

(local-defthmd eab-1
  (implies (and (not (specialp))
                (= (expgtinf) 0)
		(<= (+ (ea) (eb) 1023) 0))
	   (equal (eab)
	          (+ (exp11) (expinc) -1023)))
  :hints (("Goal" :in-theory (enable case-1-1 expinc bvecp expgtinf exp11 eab))))

(local-defthmd eab-2
  (implies (and (not (specialp))
                (= (expgtinf) 0)
		(> (+ (ea) (eb) 1023) 0))
	   (equal (eab)
	          (+ (exp11) (expinc) -1023)))
  :hints (("Goal" :in-theory (enable case-2-rewrite expinc bvecp expgtinf exp11 eab))))

(defthmd eab-not-expgtinf
  (implies (and (not (specialp))
                (= (expgtinf) 0))
	   (equal (eab)
	          (+ (exp11) (expinc) -1023)))
  :hints (("Goal" :use (eab-1 eab-2))))

(local-defthmd ab-hugepos-1
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (>= (abs (b)) (expt 2 4096)))
  :hints (("Goal" :use (sb eb expab-bound bvecp-expb b-val)
                  :in-theory (enable hugepos-rewrite)
		  :nonlinearp t)))

(local-defthmd ab-hugepos-2
  (implies (not (specialp))
           (>= (abs (a)) (spd (dp))))
  :hints (("Goal" :use (expab-bound bvecp-expa bvecp-mana)
                  :in-theory (e/d (ea sa spd dp bias a-val) (abs))
		  :nonlinearp t)))

(local-defthmd ab-hugepos-3
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (>= (abs (* (a) (b))) (expt 2 1025)))
  :hints (("Goal" :use (abs-prod-1 ab-hugepos-1 ab-hugepos-2)
                  :in-theory (enable lpn bias dp)
		  :nonlinearp t)))

(local-defthmd eab-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (expshft) 2047))
	   (> (+ (ea) (eb) 1023) 0))
  :hints (("Goal" :in-theory (enable case-1-10 rexpshft))))

(local-defthmd eab-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (expshft) 2047))
           (>= (eab) 1025))
  :hints (("Goal" :use (eab-3)
		  :in-theory (enable lexpinc case-2-rewrite eab))))

(local-defthmd eab-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (expshft) 2047))
           (natp (frac105)))
  :hints (("Goal" :use (eab-3 eab-4)
		  :in-theory (enable case-2-rewrite lfrac105))))

(local-defthmd eab-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (expshft) 2047))
           (>= (abs (* (a) (b))) (expt 2 1025)))
  :hints (("Goal" :use (eab-4 eab-5)
                  :nonlinearp t
		  :in-theory (e/d (unround-a) (abs)))))

(defthmd eab-expgtinf
  (implies (and (not (specialp))
                (= (expgtinf) 1))
           (>= (abs (* (a) (b))) (expt 2 1025)))
  :hints (("Goal" :in-theory (enable expgtinf) :use (ab-hugepos-3 eab-6))))

(local-defthm hugepos-fused
  (implies (and (not (specialp))
                (= (fused) 1))
           (equal (hugeposscale) 0))
  :hints (("Goal" :in-theory (enable input-constraints hugeposscale)
                  :use (input-constraints-lemma))))

(local-defthm fused-1
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 1))
	   (>= (+ (eab) (1- (expt 2 10)))
	       (expt 2 11)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eab cat bitn-bits exp11 expinf expgtinf specialp expovfl)
                  :use (expinc-0-1 eab-4 eab-5
		        (:instance bits-plus-bits (x (expshft)) (n 11) (p 10) (m 0))
		        (:instance bitn-plus-bits (x (expshft)) (n 11) (m 10))))))

(defthm rat-a-b
  (rationalp (abs (* (a) (b))))
  :rule-classes (:type-prescription :rewrite))

(defthm fused-expofvl
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 1))
	   (and (>= (abs (* (a) (b)))
	            (expt 2 (1+ (expt 2 10))))
		(= (bitn (flags) 4)
		   0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bitn-bits specialp flags flags-fma unround-a) (abs))
                  :nonlinearp t
                  :use (fused-1 bvecp-frac105))))

(local-defthmd fused-2
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bits (data) 115 105)
	          (bits (+ (expinc) (exp11)) 10 0)))
  :hints (("Goal" :in-theory (enable bitn-bits exp11 expgtinf expinf specialp expovfl data data-fma)
                  :use (expinc-0-1
		        (:instance bits-plus-bits (x (expshft)) (n 11) (p 10) (m 0))
		        (:instance bitn-plus-bits (x (expshft)) (n 11) (m 10))))))

(defthm natp-expshft
  (natp (expshft))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (leftshft-lemma rightshft-lemma)
                  :in-theory (enable lexpshft rexpshft))))

(local-defthm fused-3
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0)
		(= (exp11) (1- (expt 2 11))))
	   (equal (expinf) 1))
  :hints (("Goal" :in-theory (enable bvecp expinf expgtinf specialp expovfl exp11))))

(local-defthmd bvecp-exp11
  (bvecp (exp11) 11)
  :hints (("Goal" :in-theory (enable exp11))))

(local-defthmd fused-4
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bits (data) 115 105)
	          (+ (expinc) (exp11))))
  :hints (("Goal" :in-theory (enable specialp bvecp fused-2 expovfl )
                  :use (bvecp-exp11 fused-3 expinc-0-1))))

(local-defthmd fused-5
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bits (data) 115 105)
	          (+ (eab) (1- (expt 2 10)))))
  :hints (("Goal" :in-theory (enable specialp bvecp fused-4 expovfl )
                  :use (eab-not-expgtinf))))

(local-defthmd fused-6
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bits (data) 104 0)
	          (frac105)))
  :hints (("Goal" :in-theory (enable bitn-bits expgtinf expinf specialp expovfl data data-fma)
                  :use (bvecp-frac105))))

(local-defthmd fused-7
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bitn (flags) 4)
	          (stkshft)))
  :hints (("Goal" :use (rightshft-lemma leftshft-lemma)
                  :in-theory (enable bitn-bits expgtinf expinf specialp flags
		                     rstkshft flags-fma))))

(defthmd fused-normal
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0)
		(> (bits (data) 115 105) 0))
	   (and (equal (abs (* (a) (b)))
	               (* (expt 2 (- (bits (data) 115 105) (1- (expt 2 10))))
		          (1+ (* (expt 2 -105) (bits (data) 104 0)))))
		(equal (bitn (flags) 4)
		       0)))
  :hints (("Goal" :in-theory (e/d (unround-a fused-5 fused-6 fused-7) (abs)))))

(local-defthmd fused-8
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bits (data) 104 52)
	          (bits (frac105) 104 52)))
  :hints (("Goal" :in-theory (e/d (bvecp) (bits-bits))
                  :use (fused-6 bvecp-frac105 (:instance bits-bits (x (data)) (i 104) (j 0) (k 104) (l 52))))))

(local-defthmd fused-9
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0))
	   (equal (bits (data) 51 0)
	          (bits (frac105) 51 0)))
  :hints (("Goal" :in-theory (e/d (bvecp) (bits-bits))
                  :use (fused-6 bvecp-frac105 (:instance bits-bits (x (data)) (i 104) (j 0) (k 51) (l 0))))))

(defthm fused-subnormal
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0)
		(= (bits (data) 115 105) 0))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (data) 104 52))
		    (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (data) 104 52))))
		(iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
		           (bits (data) 104 52))
		        (abs (* (a) (b))))
	             (and (equal (bits (data) 51 0)
		                 0)
	                  (equal (bitn (flags) 4)
		                 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (fused-5 fused-8 fused-9 fused-7) (abs))
                  :use (unround-b))))
