(in-package "RTL")

(include-book "product")

(defund ea ()
  (if (= (expa) 0)
      (- 1 (1- (expt 2 10)))
    (- (expa) (1- (expt 2 10)))))

(defund eb ()
  (if (= (expb) 0)
      (- 1 (1- (expt 2 10)))
    (- (expb) (1- (expt 2 10)))))

(in-theory (disable (ea) (eb)))

(defthmd bvecp-expa
  (bvecp (expa) 11)
  :hints (("Goal" :in-theory (enable expf dp) :use (a-fields))))

(defthmd bvecp-expb
  (bvecp (expb) 11)
  :hints (("Goal" :in-theory (enable expf dp) :use (b-fields))))

(defthm integerp-ea
  (integerp (ea))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable ea bvecp) :use (bvecp-expa))))

(defthm integerp-eb
  (integerp (eb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable eb bvecp) :use (bvecp-expb))))

(defund a () (decode (opaz) (dp)))

(defund b () (decode (opbz) (dp)))

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

(defthmd b-val
  (implies (not (specialp))
           (equal (abs (b))
                  (* (expt 2 (- (eb) 52))
                     (sb))))
  :hints (("Goal" :in-theory (enable decode ndecode ddecode specialp sa sb ea eb a b dp prec manf sigf)
                  :use (b-fields b-normp-denormp))))

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

(local-defthmd si-expaint-1
  (implies (= (expa) 0)
           (equal (si (expint (expa)) 12)
                  (1- (ea))))
  :hints (("Goal" :in-theory (enable ea cat bvecp expint si))))

(local-defthmd si-expaint-2
  (implies (not (= (expa) 0))
           (equal (bits (expint (expa)) 9 0)
                  (bits (expa) 9 0)))
  :hints (("Goal" :in-theory (enable bvecp expint)
                  :use (bvecp-expa
		        (:instance bits-plus-bitn (x (expa)) (n 9) (m 0))
			(:instance bits-plus-bitn (x (expint (expa))) (n 9) (m 0))))))

(local-defthmd si-expaint-3
  (implies (not (= (expa) 0))
           (bvecp (expint (expa)) 12))
  :hints (("Goal" :in-theory (enable expint))))

(local-defthmd si-expaint-4
  (implies (not (= (expa) 0))
           (and (equal (bitn (expint (expa)) 11)
	               (lognot1 (bitn (expa) 10)))
		(equal (bitn (expint (expa)) 10)
	               (lognot1 (bitn (expa) 10)))))
  :hints (("Goal" :in-theory (enable expint))))

(local-defthmd si-expaint-5
  (implies (not (= (expa) 0))
           (equal (expint (expa))
	          (+ (* (expt 2 11) (lognot1 (bitn (expa) 10)))
		     (* (expt 2 10) (lognot1 (bitn (expa) 10)))
		     (bits (expa) 9 0))))
  :hints (("Goal" :in-theory (enable si-expaint-2 si-expaint-3 si-expaint-4)
                  :use ((:instance bitn-plus-bits (x (expint (expa))) (n 11) (m 0))
		        (:instance bitn-plus-bits (x (expint (expa))) (n 10) (m 0))))))

(local-defthmd si-expaint-6
  (implies (and (not (= (expa) 0))
                (= (bitn (expa) 10) 0))
           (equal (si (expint (expa)) 12)
                  (1- (ea))))
  :hints (("Goal" :in-theory (enable si-expaint-5 ea si)
                  :use (si-expaint-4 bvecp-expa
                        (:instance bitn-plus-bits (x (expa)) (n 10) (m 0))))))

(local-defthmd si-expaint-7
  (implies (and (not (= (expa) 0))
                (= (bitn (expa) 10) 1))
           (equal (si (expint (expa)) 12)
                  (1- (ea))))
  :hints (("Goal" :in-theory (enable si-expaint-5 ea si)
                  :use (si-expaint-4 bvecp-expa
                        (:instance bitn-plus-bits (x (expa)) (n 10) (m 0))))))

 (defthmd si-expaint
  (equal (si (expint (expa)) 12)
         (1- (ea)))
  :hints (("Goal" :use (si-expaint-1 si-expaint-6 si-expaint-7
                        (:instance bitn-0-1 (x (expa)) (n 10))))))

(local-defthmd si-expbint-1
  (implies (= (expb) 0)
           (equal (si (expint (expb)) 12)
                  (1- (eb))))
  :hints (("Goal" :in-theory (enable eb cat bvecp expint si))))

(local-defthmd si-expbint-2
  (implies (not (= (expb) 0))
           (equal (bits (expint (expb)) 9 0)
                  (bits (expb) 9 0)))
  :hints (("Goal" :in-theory (enable bvecp expint)
                  :use (bvecp-expb
		        (:instance bits-plus-bitn (x (expb)) (n 9) (m 0))
			(:instance bits-plus-bitn (x (expint (expb))) (n 9) (m 0))))))

(local-defthmd si-expbint-3
  (implies (not (= (expb) 0))
           (bvecp (expint (expb)) 12))
  :hints (("Goal" :in-theory (enable expint))))

(local-defthmd si-expbint-4
  (implies (not (= (expb) 0))
           (and (equal (bitn (expint (expb)) 11)
	               (lognot1 (bitn (expb) 10)))
		(equal (bitn (expint (expb)) 10)
	               (lognot1 (bitn (expb) 10)))))
  :hints (("Goal" :in-theory (enable expint))))

(local-defthmd si-expbint-5
  (implies (not (= (expb) 0))
           (equal (expint (expb))
	          (+ (* (expt 2 11) (lognot1 (bitn (expb) 10)))
		     (* (expt 2 10) (lognot1 (bitn (expb) 10)))
		     (bits (expb) 9 0))))
  :hints (("Goal" :in-theory (enable si-expbint-2 si-expbint-3 si-expbint-4)
                  :use ((:instance bitn-plus-bits (x (expint (expb))) (n 11) (m 0))
		        (:instance bitn-plus-bits (x (expint (expb))) (n 10) (m 0))))))

(local-defthmd si-expbint-6
  (implies (and (not (= (expb) 0))
                (= (bitn (expb) 10) 0))
           (equal (si (expint (expb)) 12)
                  (1- (eb))))
  :hints (("Goal" :in-theory (enable si-expbint-5 eb si)
                  :use (si-expbint-4 bvecp-expb
                        (:instance bitn-plus-bits (x (expb)) (n 10) (m 0))))))

(local-defthmd si-expbint-7
  (implies (and (not (= (expb) 0))
                (= (bitn (expb) 10) 1))
           (equal (si (expint (expb)) 12)
                  (1- (eb))))
  :hints (("Goal" :in-theory (enable si-expbint-5 eb si)
                  :use (si-expbint-4 bvecp-expb
                        (:instance bitn-plus-bits (x (expb)) (n 10) (m 0))))))

 (defthmd si-expbint
  (equal (si (expint (expb)) 12)
         (1- (eb)))
  :hints (("Goal" :use (si-expbint-1 si-expbint-6 si-expbint-7
                        (:instance bitn-0-1 (x (expb)) (n 10))))))

(defthm si-expprodint-1
  (integerp (si (expint (expa)) 12))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si expint))))

(local-defthm si-expprodint-2
  (integerp (si (expint (expb)) 12))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si expint))))
  
(local-defthmd si-expprodint-3
  (implies (not (specialp))
           (equal (expprodint)
	          (bits (+ (bits (si (expint (expa)) 12) 11 0) (expint (expb)) 1) 11 0)))
  :hints (("Goal" :in-theory (e/d (expprodint bits-si bits-mod) (si ACL2::|(mod (+ 1 x) y)|))
                  :use ((:instance mod-sum (b (expint (expa))) (a (1+ (expint (expb)))) (n (expt 2 12)))))))

(local-defthmd si-expprodint-4
  (implies (not (specialp))
           (equal (expprodint)
	          (bits (+ (si (expint (expa)) 12) (expint (expb)) 1) 11 0)))
  :hints (("Goal" :in-theory (e/d (si-expprodint-3 bits-mod) (si ACL2::|(mod (+ 1 x) y)|))
                  :use ((:instance mod-sum (b (si (expint (expa)) 12)) (a (1+ (expint (expb)))) (n (expt 2 12)))))))

(local-defthmd si-expprodint-5
  (implies (not (specialp))
           (equal (expprodint)
	          (bits (+ (bits (si (expint (expb)) 12) 11 0) (si (expint (expa)) 12) 1) 11 0)))
  :hints (("Goal" :in-theory (e/d (si-expprodint-4 bits-si bits-mod) (si ACL2::|(mod (+ 1 x) y)|))
                  :use ((:instance mod-sum (b (expint (expb))) (a (1+ (si (expint (expa)) 12))) (n (expt 2 12)))))))

(local-defthmd si-expprodint-6
  (implies (not (specialp))
           (equal (expprodint)
	          (bits (+ (si (expint (expb)) 12) (si (expint (expa)) 12) 1) 11 0)))
  :hints (("Goal" :in-theory (e/d (si-expprodint-5 bits-mod) (si ACL2::|(mod (+ 1 x) y)|))
                  :use ((:instance mod-sum (b (si (expint (expb)) 12)) (a (1+ (si (expint (expa)) 12))) (n (expt 2 12)))))))

(local-defthmd si-expprodint-7
  (implies (not (specialp))
           (equal (expprodint)
	          (bits (1- (+ (ea) (eb))) 11 0)))
  :hints (("Goal" :in-theory (enable si-expprodint-6 si-expaint si-expbint))))

(local-defthmd si-expprodint-8
  (implies (not (specialp))
           (and (<= (expa) (- (expt 2 11) 2))
	        (<= (expb) (- (expt 2 11) 2))))
  :hints (("Goal" :use (a-fields b-fields bvecp-expa bvecp-expb a-normp-denormp b-normp-denormp normp denormp)
                  :in-theory (enable bvecp normp denormp dp expf prec))))

(defthmd si-expprodint
  (implies (not (specialp))
           (equal (si (expprodint) 12)
	          (1- (+ (ea) (eb)))))
  :hints (("Goal" :use (si-expprodint-8 bvecp-expa bvecp-expb
                        (:instance si-bits (x (1- (+ (ea) (eb)))) (n 12)))
                  :in-theory (enable bvecp si-expprodint-7 ea eb))))

(defthmd bvecp-expprodint
  (bvecp (expprodint) 12)
  :hints (("Goal" :in-theory (enable expprodint))))

(local-defthmd expbiasedzero-1
  (implies (not (specialp))
           (equal (expbiasedzero)
	          (if (= (si (expprodint) 12) (- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (bvecp-expprodint
                        (:instance bitn-plus-bits (x (expprodint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expprodint)) (n 10) (m 0)))
                  :in-theory (enable expbiasedzero bvecp si))))

(defthmd expbiasedzero-rewrite
  (implies (not (specialp))
           (equal (expbiasedzero)
	          (if (= (+ (ea) (eb) (1- (expt 2 10))) 0)
		      1 0)))
  :hints (("Goal" :use (bvecp-expprodint)
                  :in-theory (enable expbiasedzero-1 si-expprodint))))

(local-defthmd expbiasedneg-1
  (implies (not (specialp))
           (equal (expbiasedneg)
	          (if (< (si (expprodint) 12) (- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (bvecp-expprodint
                        (:instance bits-bounds (x (expprodint)) (i 9) (j 0))
                        (:instance bitn-plus-bits (x (expprodint)) (n 11) (m 10))
                        (:instance bitn-plus-bits (x (expprodint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expprodint)) (n 10) (m 0)))
                  :in-theory (enable expbiasedneg bvecp si))))

(defthmd expbiasedneg-rewrite
  (implies (not (specialp))
           (equal (expbiasedneg)
	          (if (< (+ (ea) (eb) (1- (expt 2 10))) 0)
		      1 0)))
  :hints (("Goal" :use (bvecp-expprodint)
                  :in-theory (enable expbiasedneg-1 si-expprodint))))

(defund expdeficit ()
  (bits (+ (+ (+ (lognot (expa)) (lognot (expb))) 1)
           (logand1 (log<> (expa) 0) (log<> (expb) 0)))
        9 0))

(defund rshift ()
  (let ((shift (bits (expdeficit) 5 0)))
    (if1 (log<> (bits (expdeficit) 9 6) 0)
         (setbits shift 6 5 1 31)
         shift)))

(defund prod0 () (setbits (bits 0 106 0) 107 106 1 (prod)))

(defund rprodshft () (bits (ash (prod0) (- (rshift))) 105 0))

(defund rfrac105 () (bits (rprodshft) 104 0))

(defund rexpshftint () (bits 3072 11 0))

(defund rexpinc ()
  (logand1 (bitn (prod) 105)
           (log= (rshift) 1)))

(defund stkmaskfma () (rightshft-loop-0 0 (rshift) (bits 0 62 0)))

(defund rstkfma ()
  (log<> (logand (prod) (ash (stkmaskfma) (- 1)))
         0))

(defund rstkmask ()
  (setbits (bits 4503599627370495 106 0)
           107 106 52 (bits (stkmaskfma) 54 0)))

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
  (implies (not (eql (logior1 (expbiasedzero) (expbiasedneg)) 0))
           (and (equal (expshftint) (rexpshftint))
	        (equal (expinc) (rexpinc))
	        (equal (frac105) (rfrac105))
	        (equal (stkfma) (rstkfma))
	        (equal (lsb) (rlsb))
	        (equal (grd) (rgrd))
	        (equal (stk) (rstk))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(expdeficit rshift prod0 rprodshft rfrac105 rexpshftint rexpinc stkmaskfma rstkfma rstkmask rstk rgrdmask
	                rlsb rgrd expshftint expinc frac105 stkfma lsb grd stk rightshft))))

(in-theory (disable (expdeficit) (rshift) (prod0) (rprodshft) (rfrac105) (rexpshftint) (rexpinc) (stkmaskfma) (rstkfma)
                    (rstkmask) (rstk) (rgrdmask) (rlsb) (rgrd)))


(defund expdiffint ()
  (bits (+ (- (+ (expint (expa)) (expint (expb))) (clz*)) 1)
        11 0))

(defund expprodm1int () (bits (+ (expint (expa)) (expint (expb))) 11 0))

(defund expdiffbiasedzero () (log= (expdiffint) 3072))

(defund expdiffbiasedneg () (log= (bits (expdiffint) 11 10) 2))

(defund expdiffbiasedpos ()
  (logand1 (lognot1 (expdiffbiasedzero))
           (lognot1 (expdiffbiasedneg))))

(defund lshift ()
  (bits (if1 (expdiffbiasedzero) (- (clz*) 1)
            (if1 (expdiffbiasedpos) (clz*) (expprodm1int)))
        5 0))

(defund lprodshft () (bits (ash (prod) (lshift)) 105 0))

(defund lexpshftint ()
  (bits (if1 (expdiffbiasedpos) (expdiffint) 3072)
        11 0))

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
           (logand1 (expdiffbiasedzero) (sub2norm))))

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
  (implies (eql (logior1 (expbiasedzero) (expbiasedneg)) 0)
           (and (equal (expshftint) (lexpshftint))
	        (equal (expinc) (lexpinc))
	        (equal (frac105) (lfrac105))
	        (equal (stkfma) 0)
	        (equal (lsb) (llsb))
	        (equal (grd) (lgrd))
	        (equal (stk) (lstk))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(expdiffint expdiffbiasedzero expdiffbiasedneg expdiffbiasedpos lshift lprodshft lfrac105 ovfmask mulovf
	                sub2norm lexpshftint lexpinc stkmaskfma lstkmask lstk lsbmask lgrdmask llsb lgrd expprodm1int expshftint
			expinc frac105 stkfma lsb grd stk leftshft))))

(in-theory (disable (expdeficit) (rshift) (prod0) (rprodshft) (rfrac105) (rexpshftint) (rexpinc) (stkmaskfma) (rstkfma)
                    (rstkmask) (rstk) (rgrdmask) (rlsb) (rgrd)))


(defund expdiffint ()
  (bits (+ (- (+ (expint (expa)) (expint (expb))) (clz*)) 1)
        11 0))

(defund expprodm1int () (bits (+ (expint (expa)) (expint (expb))) 11 0))

(defund expdiffbiasedzero () (log= (expdiffint) 3072))

(defund expdiffbiasedneg () (log= (bits (expdiffint) 11 10) 2))

(defund expdiffbiasedpos ()
  (logand1 (lognot1 (expdiffbiasedzero))
           (lognot1 (expdiffbiasedneg))))

(defund lshift ()
  (bits (if1 (expdiffbiasedzero) (- (clz*) 1)
            (if1 (expdiffbiasedpos) (clz*) (expprodm1int)))
        5 0))

(defund lprodshft () (bits (ash (prod) (lshift)) 105 0))

(defund lexpshftint ()
  (bits (if1 (expdiffbiasedpos) (expdiffint) 3072)
        11 0))

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
           (logand1 (expdiffbiasedzero) (sub2norm))))

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
  (implies (eql (logior1 (expbiasedzero) (expbiasedneg)) 0)
           (and (equal (expshftint) (lexpshftint))
	        (equal (expinc) (lexpinc))
	        (equal (frac105) (lfrac105))
	        (equal (stkfma) 0)
	        (equal (lsb) (llsb))
	        (equal (grd) (lgrd))
	        (equal (stk) (lstk))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(expdiffint expdiffbiasedzero expdiffbiasedneg expdiffbiasedpos lshift lprodshft lfrac105 ovfmask mulovf
	                sub2norm lexpshftint lexpinc stkmaskfma lstkmask lstk lsbmask lgrdmask llsb lgrd expprodm1int expshftint
			expinc frac105 stkfma lsb grd stk leftshft))))

(in-theory (disable (expdiffint) (expdiffbiasedzero) (expdiffbiasedneg) (expdiffbiasedpos) (lshift) (lprodshft) (lfrac105) (ovfmask)
                    (mulovf) (sub2norm) (lexpshftint) (lexpinc) (stkmaskfma) (lstkmask) (lstk) (lsbmask) (lgrdmask) (llsb) (lgrd)
		    (expprodm1int)))

(local-defthmd expdeficit-0
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expa) 0)
		(= (expb) 0))
	   (equal (expdeficit)
	          (1- (expt 2 10))))
  :hints (("Goal" :in-theory (enable expdeficit lognot))))

(local-defthmd expdeficit-1
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(> (expb) 0))
	   (equal (expdeficit)
	          (mod (- (+ (expa) (expb))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable bits-mod expdeficit ea eb bvecp lognot)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-2
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(> (expb) 0))
	   (equal (- (+ (expa) (expb)))
	          (- -2046 (+ (ea) (eb)))))
  :hints (("Goal" :in-theory (enable ea eb bvecp)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-3
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(> (expb) 0))
	   (equal (expdeficit)
	          (mod (- -2046 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (expdeficit-1 expdeficit-2))))

(local-defthmd expdeficit-4
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(> (expb) 0))
	   (equal (expdeficit)
	          (mod (- 2 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable expdeficit-3)
                  :use ((:instance mod-mult (a 2) (m (- -2046 (+ (ea) (eb)))) (n 1024))))))

(local-defthmd expdeficit-5
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expa) 0)
		(> (expb) 0))
	   (equal (expdeficit)
	          (mod (- (+ 1 (expb))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable bits-mod expdeficit ea eb bvecp lognot)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-6
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expa) 0)
		(> (expb) 0))
	   (equal (- (+ 1 (expb)))
	          (- -2046 (+ (ea) (eb)))))
  :hints (("Goal" :in-theory (enable ea eb bvecp)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-7
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expa) 0)
		(> (expb) 0))
	   (equal (expdeficit)
	          (mod (- -2046 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (expdeficit-5 expdeficit-6))))

(local-defthmd expdeficit-8
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expa) 0)
		(> (expb) 0))
	   (equal (expdeficit)
	          (mod (- 2 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable expdeficit-7)
                  :use ((:instance mod-mult (a 2) (m (- -2046 (+ (ea) (eb)))) (n 1024))))))

(local-defthmd expdeficit-9
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(= (expb) 0))
	   (equal (expdeficit)
	          (mod (- (+ 1 (expa))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable bits-mod expdeficit ea eb bvecp lognot)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-10
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(= (expb) 0))
	   (equal (- (+ 1 (expa)))
	          (- -2046 (+ (ea) (eb)))))
  :hints (("Goal" :in-theory (enable ea eb bvecp)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-11
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(= (expb) 0))
	   (equal (expdeficit)
	          (mod (- -2046 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (expdeficit-9 expdeficit-10))))

(local-defthmd expdeficit-12
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (> (expa) 0)
		(= (expb) 0))
	   (equal (expdeficit)
	          (mod (- 2 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable expdeficit-11)
                  :use ((:instance mod-mult (a 2) (m (- -2046 (+ (ea) (eb)))) (n 1024))))))

(local-defthmd expdeficit-13
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (not (and (= (expa) 0) (= (expb) 0))))
	   (equal (expdeficit)
	          (mod (- 2 (+ (ea) (eb))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (expdeficit-4 expdeficit-8 expdeficit-12 bvecp-expa bvecp-expb))))

(local-defthmd expdeficit-14
  (implies (and (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
                (not (and (= (expa) 0) (= (expb) 0))))
	   (equal (expdeficit)
	          (mod (- 1 (+ (ea) (eb) (1- (expt 2 10)))) (expt 2 10))))
  :hints (("Goal" :in-theory (enable expdeficit-13)
                  :use ((:instance mod-mult (a 1) (m (- 2 (+ (ea) (eb)))) (n 1024))))))

(defthmd expdeficit-rewrite
  (implies (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
	   (equal (expdeficit)
	          (if (and (= (expa) 0) (= (expb) 0))
		      (1- (expt 2 10))
		    (- 1 (+ (ea) (eb) (1- (expt 2 10)))))))
  :hints (("Goal" :in-theory (enable expdeficit-0 expdeficit-14 bvecp ea eb)
                  :use (bvecp-expa bvecp-expb))))

(defthmd expshftint-1
  (implies (not (specialp))
           (not (equal (bits (expshftint) 11 10) 2)))
  :hints (("Goal" :cases ((eql (logior1 (expbiasedzero) (expbiasedneg)) 0))
                  :in-theory (enable rightshft-lemma leftshft-lemma lexpshftint
                                     rexpshftint expdiffbiasedpos expdiffbiasedneg expdiffbiasedzero))))

(defthmd bvecp-expshftint
  (bvecp (expshftint) 12)
  :hints (("Goal" :cases ((eql (logior1 (expbiasedzero) (expbiasedneg)) 0))
                  :in-theory (enable rightshft-lemma leftshft-lemma lexpshftint rexpshftint))))

(defthmd expshftint-bound
  (implies (not (specialp))
           (>= (si (expshftint) 12) (- (expt 2 10))))
  :hints (("Goal" :use (expshftint-1 bvecp-expshftint
                        (:instance bitn-0-1 (x (expshftint)) (n 11))
                        (:instance bitn-0-1 (x (expshftint)) (n 10))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 10) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))
                        (:instance bits-bounds (x (expshftint)) (i 9) (j 0)))
                  :in-theory (enable si))))

(defthmd expzero-rewrite
  (implies (not (specialp))
           (equal (expzero)
	          (if (= (si (expshftint) 12) (- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (expshftint-1 bvecp-expshftint
                        (:instance bitn-0-1 (x (expshftint)) (n 11))
                        (:instance bitn-0-1 (x (expshftint)) (n 10))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 10) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))
                        (:instance bits-bounds (x (expshftint)) (i 9) (j 0)))
                  :in-theory (enable expzero si))))

(defthmd expmax-rewrite
  (implies (not (specialp))
           (equal (expmax)
	          (if (= (si (expshftint) 12) (- (expt 2 10) 2))
		      1 0)))
  :hints (("Goal" :use (expshftint-1 bvecp-expshftint
                        (:instance bitn-0-1 (x (expshftint)) (n 11))
                        (:instance bitn-0-1 (x (expshftint)) (n 10))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 10) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))
                        (:instance bits-bounds (x (expshftint)) (i 9) (j 0)))
                  :in-theory (enable expmax si))))

(defthmd expinf-rewrite
  (implies (not (specialp))
           (equal (expinf)
	          (if (= (si (expshftint) 12) (1- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (expshftint-1 bvecp-expshftint
                        (:instance bitn-0-1 (x (expshftint)) (n 11))
                        (:instance bitn-0-1 (x (expshftint)) (n 10))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 10) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))
                        (:instance bits-bounds (x (expshftint)) (i 9) (j 0)))
                  :in-theory (enable expinf si))))

(defthmd expgtinf-rewrite
  (implies (not (specialp))
           (equal (expgtinf)
	          (if (> (si (expshftint) 12) (1- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (expshftint-1 bvecp-expshftint
                        (:instance bitn-0-1 (x (expshftint)) (n 11))
                        (:instance bitn-0-1 (x (expshftint)) (n 10))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 10) (m 0))
                        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))
                        (:instance bits-bounds (x (expshftint)) (i 9) (j 0)))
                  :in-theory (enable expgtinf si))))

(defund eab ()
  (+ (si (expshftint) 12)
     (expinc)
     1))

(in-theory (disable (eab)))

(defthmd expinc-0-1
  (implies (not (specialp))
           (bitp (expinc)))
  :hints (("Goal" :cases ((eql (logior1 (expbiasedzero) (expbiasedneg)) 0))
                  :in-theory (enable rightshft-lemma leftshft-lemma lexpinc rexpinc))))  

(defthm integerp-eab
  (implies (not (specialp))
           (integerp (eab)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si lexpshftint rexpshftint eab) :use (rightshft-lemma leftshft-lemma expinc-0-1))))

(defthmd eab-bound
  (implies (not (specialp))
           (>= (+ (eab) (1- (expt 2 10))) 0))
  :hints (("Goal" :use (expinc-0-1 expshftint-bound)
                  :in-theory (enable eab))))

(local-defthmd case-1-1
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (si (expshftint) 12) -1024))
  :hints (("Goal" :use (rightshft-lemma)
                  :in-theory (enable si expbiasedzero-rewrite expbiasedneg-rewrite rexpshftint))))

(local-defthmd case-1-2
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (+ (eab) 1023) (expinc)))
  :hints (("Goal" :in-theory (enable case-1-1 eab))))

(local-defthmd case-1-3
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (bvecp (expdeficit) 10))
  :hints (("Goal" :in-theory (enable expdeficit))))

(defthmd bvecp-rshift
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (bvecp (rshift) 6))
  :hints (("Goal" :in-theory (enable rshift))))

(local-defthmd case-1-5
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(>= (expdeficit) 64))
	   (member (rshift) '(62 63)))
  :hints (("Goal" :in-theory (enable rshift)
                  :use (case-1-3 bvecp-rshift
		        (:instance bits-plus-bits (x (expdeficit)) (n 9) (p 6) (m 0))
			(:instance bits-bounds (x (expdeficit)) (i 5) (j 0))
			(:instance bits-plus-bitn (x (rshift)) (n 5) (m 0))))))

(local-defthmd case-1-6
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (expdeficit) 64))
	   (equal (rshift) (expdeficit)))
  :hints (("Goal" :in-theory (enable rshift)
                  :use (case-1-3 bvecp-rshift
		        (:instance bits-plus-bits (x (expdeficit)) (n 9) (p 6) (m 0))
			(:instance bits-bounds (x (expdeficit)) (i 5) (j 0))
			(:instance bits-plus-bitn (x (rshift)) (n 5) (m 0))))))

(local-defthmd case-1-7
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (and (> (rshift) 0) (< (rshift) 64)))
  :hints (("Goal" :in-theory (enable expdeficit-rewrite)
                  :use (case-1-5 case-1-6))))

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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkmaskfma)
	          (1- (expt 2 (rshift)))))
  :hints (("Goal" :in-theory (enable bvecp stkmaskfma)
                  :use (bvecp-rshift (:instance case-1-8 (shift (rshift)) (i 0))))))

(defthm case-1-10
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (equal (expshftint) (rexpshftint))
	        (equal (expinc) (rexpinc))
	        (equal (frac105) (rfrac105))
	        (equal (stkfma) (rstkfma))
	        (equal (lsb) (rlsb))
	        (equal (grd) (rgrd))
	        (equal (stk) (rstk))))
  :hints (("Goal" :use (rightshft-lemma)
                  :in-theory (enable expbiasedzero-rewrite expbiasedneg-rewrite))))

(defthmd case-1-11
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkfma)
	          (if (= (bits (prod) (- (rshift) 2) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable bvecp ash-rewrite bits-mod case-1-9 rstkfma)
                  :cases ((= (rshift) 0))
                  :use (bvecp-rshift
		        (:instance logand-bits (x (prod)) (k 0) (n (rshift)))))))

(defthmd bvecp-prod
  (implies (not (specialp))
           (bvecp (prod) 106))
  :hints (("Goal" :use (bvecp-mana bvecp-manb)
                  :nonlinearp t
                  :in-theory (enable bvecp sa sb prod-rewrite))))

(defthmd case-1-12
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkfma)
	          (if (= (bits (prod0) (1- (rshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable bvecp prod0 cat case-1-11)
                  :cases ((= (rshift) 0))
                  :use (bvecp-prod (:instance bits-shift-up-2 (x (prod)) (k 1) (i (- (rshift) 2)))))))

(local-defthmd case-1-13
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (rprodshft)
	          (bits (prod0) (+ 105 (rshift)) (rshift))))
  :hints (("Goal" :use (case-1-7 (:instance bits-shift-down-1 (x (prod0)) (k (rshift)) (i 105) (j 0)))
                  :in-theory (enable rprodshft ash-rewrite))))

(defthmd bvecp-prod0
  (implies (not (specialp))
           (bvecp (prod0) 107))
  :hints (("Goal" :use (bvecp-prod)
                  :nonlinearp t
                  :in-theory (enable bvecp prod0 ash-rewrite))))

(defthmd case-1-14
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (rprodshft)
	          (bits (prod0) 106 (rshift))))
  :hints (("Goal" :use (case-1-7 bvecp-prod0
                        (:instance bits-plus-bits (x (prod0)) (n (+ 105 (rshift))) (p 107) (m (rshift))))
                  :in-theory (enable bvecp-bits-0 case-1-13))))

(defthmd case-1-15
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (frac105)
	          (if (= (rshift) 1)
		      (bits (prod0) 105 (rshift))
		    (bits (prod0) 106 (rshift)))))
  :hints (("Goal" :use (case-1-7 bvecp-prod0)
                  :in-theory (enable rfrac105 case-1-14 bits-bits))))

(local-defthmd case-1-16
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (> (rshift) 54))
  :hints (("Goal" :use (case-1-5 case-1-6))))

(local-defthmd case-1-17
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (equal (bits (frac105) 104 52) 0))
  :hints (("Goal" :use (case-1-16) :in-theory (enable case-1-15 bits-bits))))

(local-defthmd case-1-18
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (equal (bits (frac105) 51 0)
	          (bits (prod0) 106 (rshift))))
  :hints (("Goal" :use (case-1-16) :in-theory (enable case-1-15 bits-bits))))

(local-defthmd case-1-19
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (not (and (= (bits (frac105) 51 0) 0)
	             (= (stkfma) 0))))
  :rule-classes ()
  :hints (("Goal" :use (bvecp-prod0 prod0-non-zero case-1-18 case-1-7
                        (:instance bits-plus-bits (x (prod0)) (n 106) (p (rshift)) (m 0)))
                  :in-theory (enable case-1-12))))

(local-defthm case-1-21
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (< (abs (* (a) (b)))
	      (expt 2 (- -52 (1- (expt 2 10))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-24 bvecp-prod)
                  :in-theory (e/d (abs-prod bvecp) (abs))
		  :nonlinearp t)))

(local-defthm case-1-26
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (expdeficit) 54))
           (and (equal (+ (eab) (1- (expt 2 10))) 0)
	        (< (* (expt 2 (- -52 (1- (expt 2 10))))
		      (bits (frac105) 104 52))
		   (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))
		(not (and (= (bits (frac105) 51 0) 0)
	                  (= (stkfma) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (ab-non-zero case-1-25 case-1-19 case-1-17 case-1-20))))

(local-defthm case-1-27
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54))
           (and (<= (rshift) 54)
	        (= (rshift) (- 1 (+ (ea) (eb) (1- (expt 2 10)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-6)
                  :in-theory (enable expdeficit-rewrite))))

(local-defthm case-1-28
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (equal (eab)
	          (+ (ea) (eb) 1)))
  :hints (("Goal" :use (case-1-29 case-1-28))))

(local-defthmd case-1-31
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (rshift) 1))
           (equal (stkfma) 0))
  :hints (("Goal" :in-theory (enable case-1-12 prod0 ash-rewrite cat bitn-bits)
                  :use (bvecp-prod
		        (:instance bitn-shift-up (x (prod)) (k 1) (n -1))))))

(local-defthm case-1-38
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 1)
		(= (rshift) 1))
           (and (equal (+ (eab) (1- (expt 2 10))) 1)
	        (equal (stkfma) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-36 case-1-28 case-1-37))))

(local-defthmd case-1-39
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (+ (eab) 1023) 0))
  :hints (("Goal" :in-theory (enable rexpinc case-1-2))))

(local-defthmd case-1-40
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (+ (ea) (eb) -105 (rshift) 52)
	          (- -52 (1- (expt 2 10)))))
  :hints (("Goal" :use (case-1-27))))

(local-defthmd case-1-44
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(> (rshift) 1))
           (equal (bits (frac105) 104 52)
	          (bits (prod0) 106 (+ (rshift) 52))))
  :hints (("Goal" :in-theory (enable case-1-15)
                  :use (case-1-27))))

(local-defthmd case-1-46
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(= (bitn (prod) 105) 0)
		(= (rshift) 1))
           (equal (bitn (prod0) 106) 0))
  :hints (("Goal" :in-theory (enable bvecp prod0 ash-rewrite cat bitn-bits)
                  :use (bvecp-prod (:instance bitn-shift-up (x (prod)) (k 1) (n 105))))))

(local-defthmd case-1-47
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -52 (1- (expt 2 10))))
		     (+ (bits (frac105) 104 52)
		        (* (expt 2 (- (+ (rshift) 52)))
			   (bits (prod0) (+ (rshift) 51) 0))))))
  :hints (("Goal" :use (case-1-7 case-1-47 case-1-45 case-1-44))))

(local-defthmd case-1-49
  (implies (and (not (specialp))
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
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (equal (bits (prod0) (+ (rshift) 51) (rshift))
		  (bits (frac105) 51 0)))
  :hints (("Goal" :in-theory (enable case-1-15 bits-bits) :use (case-1-27))))

(local-defthmd case-1-53
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (expdeficit) 54)
		(or (= (bitn (prod) 105) 0)
		    (> (rshift) 1)))
           (iff (equal (bits (prod0) (+ (rshift) 51) 0)
		       0)
		(and (equal (bits (frac105) 51 0)
		            0)
	             (equal (stkfma)
		            0))))
  :hints (("Goal" :use (case-1-51 case-1-52 case-1-12))))

(local-defthm case-1-a
  (implies (and (not (specialp))
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkfma) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-1-7 case-1-26 case-1-38 case-1-39))))

(local-defthm case-1-b
  (implies (and (not (specialp))
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
	             (equal (stkfma)
		            0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
                  :use (case-1-7 case-1-26 case-1-38 case-1-39 case-1-49 case-1-50 case-1-53
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
	   (equal (clz*)
	          (if (= (expa) 0)
		      (clz53 (mana))
		    (if (= (expb) 0)
		        (clz53 (manb))
		      0))))
  :hints (("Goal" :use (clz-mana-pos clz-manb-pos si-expprodint-8) :in-theory (enable ea eb clz*))))

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
	          (- 104 (clz*))))
  :hints (("Goal" :in-theory (enable clz-rewrite bvecp clz-expo expo-sa expo-sb)
                  :use (expa-expb-0 bvecp-mana bvecp-manb expa-0-mana expb-0-manb))))

(defthmd expo-product
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (member (expo (prod))
	           (list (- 104 (clz*)) (- 105 (clz*)))))
  :hints (("Goal" :in-theory (enable sa sb prod-rewrite)
                  :use (bvecp-mana bvecp-manb expo-sa-sb (:instance expo-prod (x (sa)) (y (sb)))))))

(defthm case-2-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (equal (expshftint) (lexpshftint))
	        (equal (expinc) (lexpinc))
	        (equal (frac105) (lfrac105))
	        (equal (stkfma) 0)
	        (equal (lsb) (llsb))
	        (equal (grd) (lgrd))
	        (equal (stk) (lstk))))
  :hints (("Goal" :use (leftshft-lemma)
                  :in-theory (enable expbiasedzero-rewrite expbiasedneg-rewrite))))

(local-defthmd case-2-3
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffint)
                  (mod (+ (- (+ (expint (expa)) (expint (expb))) (clz*)) 1)
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable si expdiffint bits-mod))))

(in-theory (disable ACL2::|(mod (+ 1 x) y)|))

(local-defthmd case-2-4
  (implies (not (specialp))
           (equal (mod (+ (- (+ (expint (expa)) (expint (expb))) (clz*)) 1)
		       (expt 2 12))
                  (mod (+ (- (+ (si (expint (expa)) 12) (expint (expb))) (clz*)) 1)
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable si)
                  :use ((:instance mod-mult (m (+ (- (+ (expint (expa)) (expint (expb))) (clz*)) 1))
                                            (a -1)
					    (n (expt 2 12)))))))

(local-defthmd case-2-5
  (implies (not (specialp))
           (equal (mod (+ (- (+ (si (expint (expa)) 12) (expint (expb))) (clz*)) 1)
		       (expt 2 12))
		  (mod (+ (- (+ (si (expint (expa)) 12) (si (expint (expb)) 12)) (clz*)) 1)
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable si)
                  :use ((:instance mod-mult (m (+ (- (+ (si (expint (expa)) 12) (expint (expb))) (clz*)) 1))
                                            (a -1)
					    (n (expt 2 12)))))))

(local-defthmd case-2-6
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffint)
                  (mod (+ (- (+ (si (expint (expa)) 12) (si (expint (expb)) 12)) (clz*)) 1)
		       (expt 2 12))))
  :hints (("Goal" :use (case-2-3 case-2-4 case-2-5))))


(local-defthmd case-2-7
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffint)
                  (mod (- (+ (ea) (eb)) (1+ (clz*)))
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable si-expaint si-expbint case-2-6))))

(local-defthmd case-2-7
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffint)
                  (mod (- (+ (ea) (eb)) (1+ (clz*)))
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable si-expaint si-expbint case-2-6))))

(defthmd clz-bounds
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (natp (clz*))
	        (<= (clz*) 52)))
  :hints (("Goal" :in-theory (enable bvecp clz-expo clz-rewrite)
                  :use (expa-0-mana expb-0-manb bvecp-mana bvecp-manb
		        (:instance expo<= (x (mana)) (n 52))
		        (:instance expo<= (x (manb)) (n 52))
		        (:instance expo>= (x (mana)) (n 0))
		        (:instance expo>= (x (manb)) (n 0))))))

(defthmd si-expdiffint-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (si (expdiffint) 12)
                  (- (+ (ea) (eb)) (1+ (clz*)))))
  :hints (("Goal" :in-theory (enable bits-mod bvecp case-2-7 ea eb)
                  :use (clz-bounds bvecp-expa bvecp-expb si-expprodint-8
		        (:instance si-bits (n 12) (x (- (+ (ea) (eb)) (1+ (clz*)))))))))

(defthmd bvecp-expdiffint
  (bvecp (expdiffint) 12)
  :hints (("Goal" :in-theory (enable expdiffint))))

(local-defthmd expdiffbiasedzero-1
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffbiasedzero)
	          (if (= (si (expdiffint) 12) (- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (bvecp-expdiffint
                        (:instance bitn-plus-bits (x (expdiffint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expdiffint)) (n 10) (m 0)))
                  :in-theory (enable expdiffbiasedzero bvecp si))))

(defthmd expdiffbiasedzero-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffbiasedzero)
	          (if (= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		      1 0)))
  :hints (("Goal" :use (bvecp-expdiffint)
                  :in-theory (enable expdiffbiasedzero-1 si-expdiffint-rewrite))))

(local-defthmd expdiffbiasedneg-1
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffbiasedneg)
	          (if (< (si (expdiffint) 12) (- (expt 2 10)))
		      1 0)))
  :hints (("Goal" :use (bvecp-expdiffint
                        (:instance bits-bounds (x (expdiffint)) (i 9) (j 0))
                        (:instance bitn-plus-bits (x (expdiffint)) (n 11) (m 10))
                        (:instance bitn-plus-bits (x (expdiffint)) (n 11) (m 0))
                        (:instance bitn-plus-bits (x (expdiffint)) (n 10) (m 0)))
                  :in-theory (enable expdiffbiasedneg bvecp si))))

(defthmd expdiffbiasedneg-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffbiasedneg)
	          (if (< (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		      1 0)))
  :hints (("Goal" :use (bvecp-expdiffint)
                  :in-theory (enable expdiffbiasedneg-1 si-expdiffint-rewrite))))

(defthmd expdiffbiasedpos-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (expdiffbiasedpos)
	          (if (> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		      1 0)))
  :hints (("Goal" :use (bvecp-expdiffint expdiffbiasedzero-rewrite expdiffbiasedneg-rewrite)
                  :in-theory (enable expdiffbiasedpos))))

(local-defthmd case-2-9
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (eab)
	          (+ (ea) (eb) (- (clz*)) (expinc))))
  :hints (("Goal" :in-theory (enable expdiffbiasedpos-rewrite bvecp eab lexpshftint si-expdiffint-rewrite)
                  :use (bvecp-expdiffint))))

(local-defthmd case-2-10
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (> (+ (eab) (1- (expt 2 10)))
	      0))
  :hints (("Goal" :in-theory (enable case-2-9)
                  :use (expinc-0-1))))

(defthmd case-2-11
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift) (clz*)))
  :hints (("Goal" :in-theory (enable bvecp lshift expdiffbiasedzero-rewrite expdiffbiasedpos-rewrite)
                  :use (clz-bounds))))

(local-defthmd case-2-12
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (< (* (expt 2 (clz*)) (prod))
	      (expt 2 106)))
  :hints (("Goal" :in-theory (enable bvecp lprodshft)
                  :use (bvecp-prod clz-bounds expo-product (:instance expo>= (x (prod)) (n (- 106 (clz*)))))
		  :nonlinearp t)))

(defthmd case-2-13
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lprodshft)
	          (* (expt 2 (clz*))
		     (prod))))
  :hints (("Goal" :in-theory (enable bvecp lprodshft case-2-11 ash-rewrite)
                  :use (bvecp-prod clz-bounds case-2-12))))

(local-defthmd case-2-14
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (member (expo (lprodshft)) '(104 105)))
  :hints (("Goal" :in-theory (enable bvecp case-2-13)
                  :use (expo-product bvecp-prod clz-bounds
		        (:instance expo-shift (x (prod)) (n (clz*)))))))

(local-defthmd case-2-15
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (ovfmask)
	          (expt 2 (- 63 (clz*)))))
  :hints (("Goal" :in-theory (enable bvecp ovfmask ash-rewrite case-2-11)
                  :use (clz-bounds))))

(local-defthmd case-2-16
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (expinc)
	          (bitn (prod) (- 105 (clz*)))))
  :hints (("Goal" :in-theory (enable bitn-bits case-2-15 mulovf lexpinc expdiffbiasedzero-rewrite)
                  :use (clz-bounds
		        (:instance bitn-0-1 (x (prod)) (n (- 105 (clz*))))
		        (:instance logand-bit (x (bits (prod) 105 42)) (n (- 63 (clz*))))))))

(defthmd case-2-17
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (expinc)
	          (bitn (lprodshft) 105)))
  :hints (("Goal" :in-theory (enable case-2-13 case-2-16)
                  :use (clz-bounds bvecp-prod
		        (:instance bitn-shift-up (x (prod)) (k (clz*)) (n (- 105 (clz*))))))))

(local-defthmd case-2-18
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (expinc)
	          (mulovf)))
  :hints (("Goal" :in-theory (enable lexpinc expdiffbiasedzero-rewrite))))

(local-defthmd case-2-20
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (frac105)
	          (bits (* 2 (lprodshft)) 104 0)))
  :hints (("Goal" :in-theory (enable ash-rewrite case-2-18 bvecp lfrac105)
                  :use (case-2-19 (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd case-2-21
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (frac105)
	          (* 2 (bits (lprodshft) 103 0))))
  :hints (("Goal" :in-theory (enable case-2-20)
                  :use (case-2-19 (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))))))

(local-defthmd case-2-22
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (clz*)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (abs-prod case-2-13) (abs)))))

(local-defthmd case-2-24
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (clz*)))
		     (+ (expt 2 104) (bits (lprodshft) 103 0)))))
  :hints (("Goal" :use (case-2-22)
                  :in-theory (e/d (case-2-23) (abs)))))

(local-defthmd case-2-25
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb)) (clz*)))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-24 case-2-21) (abs)))))

(local-defthmd case-2-26
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-9 case-2-25) (abs)))))

(local-defthmd case-2-27
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 1))
           (equal (frac105)
	          (bits (lprodshft) 104 0)))
  :hints (("Goal" :in-theory (enable ash-rewrite case-2-27 bvecp lfrac105)
                  :use (case-2-19 (:instance expo-upper-bound (x (lprodshft)))))))

(defthmd case-2-29
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (clz*)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (abs-prod case-2-13) (abs)))))

(local-defthmd case-2-31
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) -104) (clz*)))
		     (+ (expt 2 105) (bits (lprodshft) 104 0)))))
  :hints (("Goal" :use (case-2-29)
                  :in-theory (e/d (case-2-30) (abs)))))

(local-defthmd case-2-32
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- (+ (ea) (eb) 1) (clz*)))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-31 case-2-28) (abs)))))

(local-defthmd case-2-33
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 1))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :in-theory (e/d (case-2-9 case-2-32) (abs)))))

(local-defthmd case-2-34
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (eab))
		     (1+ (* (expt 2 -105) (frac105))))))
  :hints (("Goal" :use (case-2-26 case-2-33 expinc-0-1))))

(local-defthmd case-2-35
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift) (1- (clz*))))
  :hints (("Goal" :in-theory (enable bvecp lshift expdiffbiasedzero-rewrite expdiffbiasedpos-rewrite)
                  :use (clz-bounds))))

(local-defthmd case-2-36
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (< (* (expt 2 (1- (clz*))) (prod))
	      (expt 2 105)))
  :hints (("Goal" :in-theory (enable bvecp lprodshft)
                  :use (bvecp-prod clz-bounds expo-product (:instance expo>= (x (prod)) (n (- 106 (clz*)))))
		  :nonlinearp t)))

(defthmd case-2-37
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lprodshft)
	          (* (expt 2 (1- (clz*)))
		     (prod))))
  :hints (("Goal" :in-theory (enable bvecp lprodshft case-2-35 ash-rewrite)
                  :use (bvecp-prod clz-bounds case-2-36))))

(local-defthmd case-2-38
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (member (expo (lprodshft)) '(104 103)))
  :hints (("Goal" :in-theory (enable bvecp case-2-37)
                  :use (expo-product bvecp-prod clz-bounds
		        (:instance expo-shift (x (prod)) (n (1- (clz*))))))))

(local-defthmd case-2-39
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (ovfmask)
	          (expt 2 (- 64 (clz*)))))
  :hints (("Goal" :in-theory (enable bvecp ovfmask ash-rewrite case-2-35)
                  :use (clz-bounds))))

(local-defthmd case-2-40
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (mulovf)
	          (bitn (prod) (- 106 (clz*)))))
  :hints (("Goal" :in-theory (enable bitn-bits case-2-39 mulovf lexpinc expdiffbiasedzero-rewrite)
                  :use (clz-bounds
		        (:instance bitn-0-1 (x (prod)) (n (- 106 (clz*))))
		        (:instance logand-bit (x (bits (prod) 105 42)) (n (- 64
                                                                             (clz*))))))))

(local-defthmd case-2-41
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (prod) (expt 2 (- 106 (clz*)))))
  :hints (("Goal" :in-theory (enable bvecp) :nonlinearp t
                  :use (clz-bounds expo-product
		        (:instance expo>= (x (prod)) (n (- 106 (clz*))))))))

(local-defthmd case-2-42
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (mulovf) 0))
  :hints (("Goal" :in-theory (enable bvecp case-2-40)
                  :use (clz-bounds case-2-41 bvecp-prod
		        (:instance bitn-plus-bits (x (prod)) (n (- 106 (clz*))) (m 0))
		        (:instance bits-bounds (x (prod)) (i (- 105 (clz*))) (j 0))
		        (:instance bitn-0-1 (x (prod)) (n (- 106 (clz*))))
		        (:instance expo>= (x (prod)) (n (- 106 (clz*))))))))

(local-defthmd case-2-43
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lexpinc)
	          (bitn (prod) (- 105 (clz*)))))
  :hints (("Goal" :in-theory (enable bitn-bits ash-rewrite sub2norm case-2-39 case-2-42 lexpinc expdiffbiasedzero-rewrite)
                  :use (clz-bounds
		        (:instance bitn-0-1 (x (prod)) (n (- 104 (clz*))))
		        (:instance logand-bit (x (bits (prod) 104 42)) (n (- 63 (clz*))))))))

(defthmd case-2-44
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (expinc)
	          (bitn (lprodshft) 104)))
  :hints (("Goal" :in-theory (enable case-2-37 case-2-43)
                  :use (clz-bounds bvecp-prod
		        (:instance bitn-shift-up (x (prod)) (k (1- (clz*))) (n (- 105 (clz*))))))))

(local-defthmd case-2-45
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -102 (expt 2 10)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (case-2-37 abs-prod) (abs))
                  :use (clz-bounds bvecp-prod))))

(defthmd case-2-46
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (frac105)
	          (* 2 (bits (lprodshft) 103 0))))
  :hints (("Goal" :in-theory (enable case-2-42 ash-rewrite bvecp lfrac105)
                  :use (case-2-38
		        (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))
		        (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd case-2-47
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (eab)
	          (+ -1023 (expinc))))
  :hints (("Goal" :in-theory (enable expdiffbiasedpos-rewrite bvecp eab lexpshftint si-expdiffint-rewrite)
                  :use (bvecp-expdiffint))))

(local-defthmd case-2-48
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 1))
	   (and (= (eab) -1022)
                (equal (abs (* (a) (b)))
    	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :hints (("Goal" :in-theory (e/d (case-2-45 case-2-46 case-2-47) (abs))
                  :use (case-2-49))))

(local-defthmd case-2-51
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (frac105)
	          (* 2 (lprodshft))))
  :hints (("Goal" :in-theory (enable case-2-46 bvecp lfrac105)
                  :use (case-2-51
		        (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd case-2-53
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
		(= (expinc) 0))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -103 (expt 2 10)))
		     (frac105))))
  :hints (("Goal" :in-theory (e/d (case-2-45 case-2-52) (abs)))))

(local-defthmd case-2-54
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (bits (+ (expint (expa)) (expint (expb))) 5 0)))
  :hints (("Goal" :in-theory (enable bits-bits lshift expprodm1int EXPDIFFBIASEDZERO-rewrite EXPDIFFBIASEDPOS-rewrite))))

(local-defthmd case-2-57
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (mod (+ (expint (expa)) (expint (expb))) 64)))
  :hints (("Goal" :in-theory (enable case-2-56 bits-mod))))

(local-defthmd case-2-57
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (mod (+ (expint (expa)) (expint (expb))) 64)))
  :hints (("Goal" :in-theory (enable case-2-56 bits-mod))))

(local-defthmd case-2-58
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (mod (+ (si (expint (expa)) 12) (expint (expb))) 64)))
  :hints (("Goal" :in-theory (enable case-2-57 si)
                  :use ((:instance mod-mult (m (+ (expint (expa)) (expint (expb)))) (a -1) (n 64))))))

(local-defthmd case-2-59
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (mod (+ (si (expint (expa)) 12) (si (expint (expb)) 12)) 64)))
  :hints (("Goal" :in-theory (enable case-2-58 si)
                  :use ((:instance mod-mult (m (+ (si (expint (expa)) 12) (expint (expb)))) (a -1) (n 64))))))

(local-defthmd case-2-60
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (mod (+ (ea) (eb) -2) 64)))
  :hints (("Goal" :in-theory (enable si-expaint si-expbint case-2-59))))

(local-defthmd case-2-61
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (mod (+ (ea) (eb) 1022) 64)))
  :hints (("Goal" :in-theory (enable case-2-60)
                  :use ((:instance mod-mult (m (+ (ea) (eb))) (a 16) (n 64))))))

(local-defthmd case-2-62
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lshift)
	          (+ (ea) (eb) 1022)))
  :hints (("Goal" :in-theory (enable case-2-61)
                  :use (clz-bounds))))

(defthmd case-2-63
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (prod) (expt 2 (- 106 (clz*)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (clz-bounds bvecp-prod expo-product (:instance expo>= (x (prod)) (n (- 106 (clz*))))))))

(defthmd lshift-bound
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (<= (lshift) (- (clz*) 2)))
  :hints (("Goal" :in-theory (enable case-2-62)
                  :use (clz-bounds))))

(defthmd case-2-65
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (* (expt 2 (lshift)) (prod))
	      (expt 2 104)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (clz-bounds bvecp-prod case-2-63 lshift-bound))))

(defthmd case-2-66
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (lprodshft)
	          (* (prod) (expt 2 (lshift)))))
  :hints (("Goal" :in-theory (enable lprodshft ash-rewrite bvecp)
                  :use (clz-bounds bvecp-prod case-2-65))))

(local-defthmd case-2-67
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (ovfmask)
	          (expt 2 (- 63 (lshift)))))
  :hints (("Goal" :in-theory (enable bvecp ovfmask ash-rewrite)
                  :use (lshift-bound clz-bounds))))

(defthmd case-2-68
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (mulovf)
	          (bitn (prod) (- 105 (lshift)))))
  :hints (("Goal" :in-theory (enable bitn-bits case-2-67 mulovf lexpinc expdiffbiasedzero-rewrite expdiffbiasedneg-rewrite)
                  :use (clz-bounds lshift-bound
		        (:instance bitn-0-1 (x (prod)) (n (- 105 (lshift))))
		        (:instance logand-bit (x (bits (prod) 105 42)) (n (- 63 (lshift))))))))

(local-defthmd case-2-69
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (expt 2 (- 106 (clz*)))
	      (expt 2 (- 105 (lshift)))))
  :hints (("Goal" :nonlinearp t
                  :use (clz-bounds lshift-bound))))

(defthmd case-2-70
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (prod) (expt 2 (- 105 (lshift)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (clz-bounds case-2-63 case-2-69))))

(defthmd case-2-71
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (mulovf) 0))
  :hints (("Goal" :in-theory (enable case-2-68 bvecp)
                  :use (case-2-70 bvecp-prod))))

(defthmd case-2-72
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (frac105)
	          (* 2 (lprodshft))))
  :hints (("Goal" :in-theory (enable case-2-71 case-2-66 ash-rewrite bvecp lfrac105)
                  :use (case-2-65 bvecp-prod
		        (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))))))

(local-defthmd case-2-73
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -102 (expt 2 10)))
		     (lprodshft))))
  :hints (("Goal" :in-theory (e/d (case-2-66 case-2-62 abs-prod) (abs))
                  :use (clz-bounds bvecp-prod))))

(local-defthmd case-2-74
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -103 (expt 2 10)))
		     (frac105))))
  :hints (("Goal" :in-theory (e/d (case-2-73 case-2-72) (abs)))))

(local-defthmd case-2-75
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (- -51 (expt 2 10)))
		     (+ (bits (frac105) 104 52)
		        (* (expt 2 -52) (bits (frac105) 51 0))))))
  :hints (("Goal" :in-theory (e/d (case-2-74) (abs))
                  :use (bvecp-frac105
		        (:instance bits-plus-bits (x (frac105)) (n 104) (p 52) (m 0))))))

(local-defthmd case-2-76
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (eab) -1023))
  :hints (("Goal" :in-theory (enable expdiffbiasedzero-rewrite expdiffbiasedpos-rewrite lexpinc bvecp eab si
                                     case-2-71 lexpshftint))))

(local-defthmd case-2-77
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
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
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkfma) 0)
		(equal (abs (* (a) (b)))
   	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :rule-classes ()
  :hints (("Goal" :use (case-2-10 case-2-34 case-2-50 case-2-55 case-2-77))))

(local-defthm case-2-b
  (implies (and (not (specialp))
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
	             (equal (stkfma)
		            0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
                  :use (case-2-10 case-2-34 case-2-50 case-2-55 case-2-77))))

(defthmd unround-a
  (implies (and (not (specialp))
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkfma) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105)))))))
  :hints (("Goal" :use (case-1-a case-2-a))))

(defthm unround-b
  (implies (and (not (specialp))
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
	                  (equal (stkfma)
		                 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
           :use (case-1-b case-2-b))))


(local-defthmd eab-1
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 0))
	   (equal (exp11)
	          (+ (expt 2 10) (expshftint))))
  :hints (("Goal" :in-theory (enable cat bvecp exp11)
                  :use (bvecp-expshftint
		        (:instance bits-bounds (x (expshftint)) (i 9) (j 0))
		        (:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 0))
			(:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))))))

(local-defthmd eab-2
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 0))
	   (equal (expgtinf) 0))
  :hints (("Goal" :in-theory (enable expgtinf))))

(local-defthmd eab-3
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 0))
	   (equal (+ (eab) (1- (expt 2 10)))
	          (+ (exp11) (* (expt 2 11) (expgtinf)) (expinc))))
  :hints (("Goal" :in-theory (enable si eab-1 eab-2 eab)
                  :use ((:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 1))))))

(local-defthmd eab-4
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 1))
	   (equal (exp11)
	          (- (expshftint) (expt 2 10))))
  :hints (("Goal" :in-theory (enable cat bvecp exp11)
                  :use (bvecp-expshftint
		        (:instance bits-bounds (x (expshftint)) (i 9) (j 0))
		        (:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 0))
			(:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))))))

(local-defthmd eab-5
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 1))
	   (equal (expgtinf) 1))
  :hints (("Goal" :in-theory (enable expgtinf))))

(local-defthmd eab-6
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 1))
	   (equal (+ (eab) (1- (expt 2 10)))
	          (+ (exp11) (* (expt 2 11) (expgtinf)) (expinc))))
  :hints (("Goal" :in-theory (enable si eab-4 eab-5 eab)
                  :use ((:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 1))))))

(local-defthmd eab-7
  (implies (not (specialp))
           (not (= (bits (expshftint) 11 10) 2)))
  :hints (("Goal" :in-theory (enable si)
                  :use (bvecp-expshftint expshftint-bound
		        (:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 1))
                        (:instance bits-bounds (x (expshftint)) (i 9) (j 0))
			(:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))))))

(local-defthmd eab-8
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 3))
	   (equal (exp11)
	          (+ (expshftint) (- (expt 2 12)) (expt 2 10))))
  :hints (("Goal" :in-theory (enable bitn-bits cat bvecp exp11)
                  :use (bvecp-expshftint
		        (:instance bits-bounds (x (expshftint)) (i 9) (j 0))
		        (:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 0))
			(:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))))))

(local-defthmd eab-9
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 3))
	   (equal (expgtinf) 0))
  :hints (("Goal" :in-theory (enable expgtinf))))

(local-defthmd eab-10
  (implies (and (not (specialp))
                (= (bits (expshftint) 11 10) 3))
	   (equal (+ (eab) (1- (expt 2 10)))
	          (+ (exp11) (* (expt 2 11) (expgtinf)) (expinc))))
  :hints (("Goal" :in-theory (enable si eab-8 eab-9 eab)
                  :use ((:instance bitn-bits (x (expshftint)) (i 11) (j 10) (k 1))))))

(defthmd eab-val
  (implies (not (specialp))
	   (equal (+ (eab) (1- (expt 2 10)))
	          (+ (exp11) (* (expt 2 11) (expgtinf)) (expinc))))
  :hints (("Goal" :in-theory (enable si eab-8 eab-9 eab)
                  :use (eab-3 eab-6 eab-7 eab-10 (:instance bvecp-member (x (bits (expshftint) 11 10)) (n 2))))))

(local-defthm fused-1
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 1))
	   (>= (+ (eab) (1- (expt 2 10)))
	       (expt 2 11)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cat bitn-bits exp11 expgtinf expinf specialp expovfl)
                  :use (eab-val expinc-0-1
		        (:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))
		        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))))))

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
		        (:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))
		        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))))))

(local-defthm fused-3
  (implies (and (not (specialp))
                (= (fused) 1)
                (= (expovfl) 0)
		(= (exp11) (1- (expt 2 11))))
	   (equal (expinf) 1))
  :hints (("Goal" :in-theory (enable cat bvecp bitn-bits expinf expgtinf expovfl exp11)
                  :use (eab-7 expinc-0-1
		        (:instance bits-bounds (x (expshftint)) (i 9) (j 0))
		        (:instance bits-plus-bits (x (expshftint)) (n 11) (p 10) (m 0))
		        (:instance bitn-plus-bits (x (expshftint)) (n 11) (m 10))))))

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
                  :use (eab-val))))

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
	          (stkfma)))
  :hints (("Goal" :cases ((eql (logior1 (expbiasedzero) (expbiasedneg)) 0))
                  :in-theory (enable rightshft-lemma leftshft-lemma bitn-bits expgtinf expinf specialp flags
		                     rstkfma flags-fma))))

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
