(in-package "RTL")

(include-book "expinc")

(defund mode ()
  (case (rmode)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

(defund modep ()
  (if (< (/ (a) (b)) 0)
      (flip-mode (mode))
    (mode)))

(in-theory (disable (mode) (modep)))

(defthm common-mode-p-modep
  (implies (not (specialp))
           (common-mode-p (modep)))
  :hints (("Goal" :in-theory (enable rmode mode modep common-mode-p flip-mode)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd rnd-modep-mode
  (implies (not (specialp))
           (equal (rnd (* (a) (b)) (mode) 53)
	          (if (< (* (a) (b)) 0)
		      (- (rnd (abs (* (a) (b))) (modep) 53))
		    (rnd (abs (* (a) (b))) (modep) 53))))
  :hints (("Goal" :in-theory (enable rnd modep mode flip-mode rmode common-mode-p)
                  :use ((:instance rnd-minus (mode (modep)) (x (abs (* (a) (b)))))
		        (:instance rne-minus (x (* (a) (b))) (n 53))
		        (:instance rtz-minus (x (* (a) (b))) (n 53))
		        (:instance raz-minus (x (* (a) (b))) (n 53))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd underflow-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
	   (>= (abs (* (a) (b))) (spn (dp))))
  :hints (("Goal" :in-theory (e/d (unround-a dp spn bias expw) (abs))
                  :cases ((<= (+ (ea) (eb) (1- (expt 2 10))) 0)))))

(defthmd underflow-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (< (abs (* (a) (b))) (spn (dp))))
  :hints (("Goal" :in-theory (e/d (dp spn bias expw) (abs))
                  :use (unround-b
		        (:instance bits-bounds (x (frac105)) (i 104) (j 52)))
                  :cases ((<= (+ (ea) (eb) (1- (expt 2 10))) 0)))))

(defthmd underflow-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0))
           (equal (underflow)
	          (if (< (abs (* (a) (b))) (spn (dp)))
		      1 0)))
  :hints (("Goal" :in-theory (e/d (underflow expzero eab dp spn bias expw) ())
                  :use (expinc-0-1 underflow-1 underflow-2 eab-bound))))

(local-defund x0 ()
  (+ (expt 2 53) (bits (frac105) 104 52)))

(local-defund z0 ()
  (* (expt 2 (- 53 (eab)))
     (abs (* (a) (b)))))

(local-in-theory (disable (x0) (z0)))

(local-defthmd norm-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (z0)
	          (+ (x0)
		     (* (expt 2 -52) (bits (frac105) 51 0)))))
  :hints (("Goal" :in-theory (e/d (x0 z0) (abs))
                  :use (unround-a bvecp-frac105 (:instance bits-plus-bits (x (frac105)) (n 104) (p 52) (m 0))))))

(local-defthmd norm-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (fl (z0)) (x0)))
  :hints (("Goal" :in-theory (enable norm-1)
                  :use ((:instance bits-bounds (x (frac105)) (i 51) (j 0)))
		  :nonlinearp t)))

(local-defthmd norm-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (stk)
	          (if (integerp (z0))
		      0 1)))	        
  :hints (("Goal" :use (bvecp-frac105 norm-1 norm-2)
                  :in-theory (enable stk-rewrite unround-a))))

(local-defthmd norm-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (expo (x0)) 53))
  :hints (("Goal" :use ((:instance expo-unique (x (x0)) (n 53))
                        (:instance bits-bounds (x (frac105)) (i 104) (j 52)))
	          :in-theory (enable x0)
		  :nonlinearp t)))

(local-defthmd norm-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (sgn (x0)) 1))
  :hints (("Goal" :in-theory (enable sgn x0)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 52))))))

(local-defthmd norm-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rtz (x0) 53)
	          (* 2 (fl (/ (x0) 2)))))
  :hints (("Goal" :in-theory (enable rtz-rewrite norm-4 norm-5))))

(local-defthmd norm-7
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rtz (x0) 53)
	          (* 2 (+ (expt 2 52) (fracunrnd)))))
  :hints (("Goal" :in-theory (enable fracunrnd x0)
                  :use (norm-6
		        (:instance bits-plus-bitn (x (frac105)) (n 104) (m 52))
		        (:instance bitn-0-1 (x (frac105)) (n 52))))))

(local-defthmd norm-8
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (fp+ (rtz (x0) 53) 53)
	          (+ (rtz (x0) 53) 2)))
  :hints (("Goal" :in-theory (enable fp+ norm-4))))

(local-defthmd norm-9
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (fp+ (rtz (x0) 53) 53)
	          (* 2 (+ (expt 2 52) (fracp1)))))
  :hints (("Goal" :in-theory (enable bvecp fracunrnd fracp1 norm-7)
                  :use (norm-8 (:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd norm-10
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (bits (x0) 52 0)
	          (bits (frac105) 104 52)))
  :hints (("Goal" :in-theory (enable x0 bits-mod)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 52))))))

(local-defthmd norm-11
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (bitn (x0) 0)
	          (grd)))
  :hints (("Goal" :in-theory (enable grd-rewrite norm-10)
                  :use (norm-8
		        (:instance bitn-bits (x (frac105)) (i 104) (j 52) (k 0))
		        (:instance bitn-bits (x (x0)) (i 52) (j 0) (k 0))))))

(local-defthmd norm-12
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (bitn (x0) 1)
	          (lsb)))
  :hints (("Goal" :in-theory (enable lsb-rewrite norm-10)
                  :use (norm-8
		        (:instance bitn-bits (x (frac105)) (i 104) (j 52) (k 1))
		        (:instance bitn-bits (x (x0)) (i 52) (j 0) (k 1))))))

(defthmd signa-rewrite
  (implies (not (specialp))
           (equal (signa)
	          (if (> (a) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable ddecode ndecode sgn specialp encodingp normp denormp decode a dp prec)
                  :use (sign-0-1 a-fields member-classa a-class a-fields
		        (:instance sgn-ndecode (x (opaz)) (f (dp)))
		        (:instance sgn-ddecode (x (opaz)) (f (dp)))))))

(defthmd signb-rewrite-fmul
  (implies (and (not (specialp))
                (= (fscale) 0))
           (equal (signb)
	          (if (> (b) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable ddecode ndecode sgn specialp encodingp normp denormp decode b dp prec)
                  :use (sign-0-1 b-fields member-classb b-class b-fields
		        (:instance sgn-ndecode (x (opbz)) (f (dp)))
		        (:instance sgn-ddecode (x (opbz)) (f (dp)))))))

(defthm fscale-opb
  (implies (= (fscale) 1)
           (equal (opb) #x3ff0000000000000))
  :hints (("Goal" :in-theory (enable input-constraints)
                  :use (input-constraints-lemma))))

(defthmd signb-rewrite-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
           (equal (signb)
	          (if (> (b) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable ddecode ndecode sgn specialp encodingp normp denormp decode b dp prec)
                  :use (sign-0-1 b-fields member-classb b-class b-fields
		        (:instance sgn-ndecode (x (opbz)) (f (dp)))
		        (:instance sgn-ddecode (x (opbz)) (f (dp)))))))

(defthmd signb-rewrite
  (implies (not (specialp))
           (equal (signb)
	          (if (> (b) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable input-constraints)
                  :use (signb-rewrite-fscale signb-rewrite-fmul input-constraints-lemma))))

(defthmd a-nonzero
  (implies (not (specialp))
           (not (equal (a) 0)))
  :hints (("Goal" :in-theory (enable ddecode ndecode sgn specialp encodingp normp denormp decode a dp prec)
                  :use (sign-0-1 a-fields member-classa a-class a-fields
		        (:instance sgn-ndecode (x (opaz)) (f (dp)))
		        (:instance sgn-ddecode (x (opaz)) (f (dp)))))))

(defthmd b-nonzero
  (implies (not (specialp))
           (not (equal (b) 0)))
  :hints (("Goal" :in-theory (enable ddecode ndecode sgn specialp encodingp normp denormp decode b dp prec)
                  :use (sign-0-1 b-fields member-classb b-class b-fields
		        (:instance sgn-ndecode (x (opbz)) (f (dp)))
		        (:instance sgn-ddecode (x (opbz)) (f (dp)))))))

(defthmd sign-rewrite
  (implies (not (specialp))
           (equal (sign)
	          (if (< (* (a) (b)) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable a-nonzero b-nonzero sign signa-rewrite signb-rewrite))))

(local-defthmd norm-13
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rndup)
	          (if (roundup-pos (x0) 53 (stk) (modep) 53)
		      1 0)))
  :hints (("Goal" :in-theory (enable sign-rewrite mode modep rmode roundup-pos rndup norm-11 norm-12
                                     stk-rewrite grd-rewrite lsb-rewrite)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthm rationalp-z0
  (rationalp (z0))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable z0))))

(local-defthmd norm-14
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (>= (z0) (expt 2 53)))
  :hints (("Goal" :in-theory (enable x0)
                  :use (norm-2))))

(local-defthmd norm-15
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 0))
	   (equal (rnd (z0) (modep) 53)
	          (rtz (x0) 53)))
  :hints (("Goal" :in-theory (enable norm-2 norm-3 norm-4 norm-11 norm-12 norm-13)
                  :use (norm-14 (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))))))

(local-defthmd norm-16
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
	   (iff (exactp (z0) 53)
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :in-theory (enable norm-2 norm-3 norm-4 norm-11 norm-12 norm-13)
                  :use (norm-14 (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))))))

(local-defthmd norm-17
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 0))
	   (and (equal (exprndinc) 0)
	        (equal (rnd (z0) (modep) 53)
		       (* 2 (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable bvecp norm-7 norm-15 exprndinc fracunrnd fracrnd))))

(local-defthmd norm-18
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1))
	   (equal (rnd (z0) (modep) 53)
	          (fp+ (rtz (x0) 53) 53)))
  :hints (("Goal" :in-theory (enable norm-2 norm-3 norm-4 norm-11 norm-12 norm-13)
                  :use (norm-14 (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))))))

(local-defthmd norm-19
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1))
	   (equal (rnd (z0) (modep) 53)
	          (* 2 (+ (expt 2 52) (fracp1)))))
  :hints (("Goal" :in-theory (enable norm-18)
                  :use (norm-9))))

(local-defthmd norm-20
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1)
		(< (fracp1) (expt 2 52)))
	   (and (equal (exprndinc) 0)
  	        (equal (rnd (z0) (modep) 53)
	               (* 2 (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable norm-19 fracp1 fracunrnd fracrnd exprndinc bvecp)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd norm-21
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1)
		(= (fracp1) (expt 2 52)))
	   (and (equal (exprndinc) 1)
  	        (equal (rnd (z0) (modep) 53)
	               (* 4 (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable norm-19 fracp1 fracunrnd fracrnd exprndinc bvecp)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd norm-22
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1))
           (<= (fracp1) (expt 2 52)))
  :hints (("Goal" :in-theory (enable norm-19 fracp1 fracunrnd fracrnd exprndinc bvecp)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd norm-23
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (z0) (modep) 53)
	          (* (expt 2 (1+ (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :use (norm-17 norm-20 norm-21 norm-22)
                  :in-theory (enable rndup))))

(defthm rationalp-abs
  (implies (rationalp x)
           (rationalp (abs x)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd norm-24
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (* (expt 2 (- 53 (eab)))
	             (rnd (abs (* (a) (b))) (modep) 53))
	          (* (expt 2 (1+ (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :use (norm-23 (:instance rnd-shift (x (abs (* (a) (b)))) (n 53) (mode (modep)) (k (- 53 (eab)))))
                  :in-theory (e/d (exprndinc z0) (abs)))))

(local-defthmd norm-25
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (* (expt 2 (- (eab) 53))
	             (expt 2 (- 53 (eab)))
	             (rnd (abs (* (a) (b))) (modep) 53))
	          (* (expt 2 (- (eab) 53))
		     (expt 2 (1+ (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :use (norm-24))))

(local-defthmd norm-26
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (abs (* (a) (b))) (modep) 53)
	          (* (expt 2 (+ (eab) -52 (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :use (norm-25)
                  :in-theory (disable abs))))

(defthmd norm-rnd
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (* (a) (b)) (mode) 53)
	          (if (= (sign) 1)
		      (- (* (expt 2 (+ (eab) -52 (exprndinc)))
		            (+ (expt 2 52) (fracrnd))))
	            (* (expt 2 (+ (eab) -52 (exprndinc)))
		       (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (e/d (sign-rewrite rnd-modep-mode norm-26) (abs)))))

(local-defthmd norm-28
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
	   (iff (exactp (* (a) (b)) 53)
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :use (norm-16
                        (:instance exactp-shift (x (abs (* (a) (b)))) (k (- 53 (eab))) (n 53)))
                  :in-theory (e/d (z0) (abs)))))

(defthm common-mode-p-mode
  (implies (not (specialp))
           (common-mode-p (mode)))
  :hints (("Goal" :in-theory (enable rmode mode common-mode-p)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd norm-exact
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (rnd (* (a) (b)) (mode) 53)
	           (* (a) (b)))
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :use (norm-28
                        (:instance rnd-exactp-b (x (* (a) (b))) (mode (mode)) (n 53))))))
