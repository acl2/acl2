(in-package "RTL")

(include-book "induct")

(defthmd sqrt-a-x
  (implies (not (specialp))
           (equal (qsqrt (a) (1+ (* 2 (n))))
                  (* (expt 2 (1+ (- (expq) (bias (f)))))
                     (qsqrt (x) (1+ (* 2 (n)))))))
  :hints (("Goal" :in-theory (enable n a-x dp sp hp p prec bias f)
                  :use (fnum-vals x-bounds
                        (:instance qsqrt-shift (x (x)) (n (1+ (* 2 (n)))) (k (1+ (- (expq) (bias (f))))))))))

(local-defthmd error-1
  (implies (not (specialp))
           (and (<= (blo (n)) (rf))
                (>= (bhi (n)) (rf))))
  :hints (("Goal" :in-theory (enable rf n inv r-bnds-inv)
                  :use ((:instance inv-lemma (j (n)))))))

(in-theory (disable (blo) (bhi)))

(defthmd quotf-error-a
  (implies (not (specialp))
           (and (<= (expt (- (quotf) (* 2/3 (expt 4 (- (n))))) 2)
	           (x))
                (>= (expt (+ (quotf) (* 2/3 (expt 4 (- (n))))) 2)
	           (x))))
  :hints (("Goal" :in-theory (enable rf quotf n)
                  :use (error-1 (:instance r-bounds (j (n)))))))

(defthmd quotf-bounds
  (implies (not (specialp))
           (and (<= (quotf) 1)
                (>= (quotf) 1/2)))
  :hints (("Goal" :in-theory (enable quotf n inv quot-bnds-inv)
                  :use ((:instance inv-lemma (j (n)))))))

(defthmd error-4
  (implies (not (specialp))
           (and (< (expt (- (quotf) (expt 4 (- (n)))) 2)
	           (x))
                (> (expt (+ (quotf) (expt 4 (- (n)))) 2)
	           (x))))
  :hints (("Goal" :in-theory (enable expt rf quotf n)
                  :nonlinearp t
                  :use (fnum-vals quotf-error-a quotf-bounds))))

(local-defthmd error-5
  (implies (not (specialp))
           (<= (expo (- (quotf) (expt 4 (- (n)))))
	       -1))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quotf-bounds (:instance expo<= (x (- (quotf) (expt 4 (- (n))))) (n -1))))))

(local-defthmd error-6
  (implies (not (specialp))
           (exactp (- (quotf) (expt 4 (- (n))))
	           (* 2 (n))))
  :hints (("Goal" :in-theory (enable quotf exactp2 n)
                  :use (fnum-vals error-5
		        (:instance exactp-<= (x (- (quotf) (expt 4 (- (n)))))
			                     (m (+ (* 2 (n)) (expo (- (quotf) (expt 4 (- (n))))) 1))
					     (n (* 2 (n))))
		        (:instance int-quot (j (n)))))))

(local-defthmd error-7
  (implies (not (specialp))
           (exactp (sig (a)) (p)))
  :hints (("Goal" :in-theory (enable exactp exactp-sig)
                  :use (exactp-a p-vals))))

(defthmd exactp-x
  (implies (not (specialp))
           (exactp (x) (p)))
  :hints (("Goal" :in-theory (enable x)
                  :use (error-7 p-vals
                        (:instance exactp-shift (x (sig (a))) (n (p)) (k -1))
                        (:instance exactp-shift (x (sig (a))) (n (p)) (k -2))))))

(local-defthmd error-9
  (implies (not (specialp))
           (< (x)
	      (* (- 1 (expt 2 (- (1+ (p)))))
	         (- 1 (expt 2 (- (1+ (p))))))))
  :hints (("Goal" :use (p-vals exactp-x x-bounds (:instance fp-2 (n (p)) (x 1) (y (x)))))))

(local-defthmd error-10
  (implies (not (specialp))
           (< (- (quotf) (expt 4 (- (n))))
	      (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :in-theory (enable n) :use (p-vals error-4 error-9) :nonlinearp t)))

(local-defthmd error-11
  (implies (not (specialp))
           (< (quotf) 1))
  :hints (("Goal" :in-theory (enable n f dp sp hp p prec)
                  :use (fnum-vals error-10)
		  :nonlinearp t)))

(local-defthmd error-12
  (implies (not (specialp))
           (<= (* (expt 4 (n)) (quotf))
	       (1- (expt 4 (n)))))
  :hints (("Goal" :in-theory (enable quotf n)
                  :use (error-11 (:instance int-quot (j (n))))
		  :nonlinearp t)))

(local-defthm error-13
  (implies (not (specialp))
           (or (= (+ (quotf) (expt 4 (- (n)))) 1)
               (<= (expo (+ (quotf) (expt 4 (- (n)))))
	           -1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quotf-bounds error-12
		        (:instance expo<= (x (+ (quotf) (expt 4 (- (n))))) (n -1))))))

(local-defthmd error-14
  (implies (not (specialp))
           (exactp (+ (quotf) (expt 4 (- (n))))
	           (* 2 (n))))
  :hints (("Goal" :in-theory (enable quotf exactp2 n)
                  :use (fnum-vals error-13
		        (:instance exactp-<= (x (+ (quotf) (expt 4 (- (n)))))
			                     (m (+ (* 2 (n)) (expo (+ (quotf) (expt 4 (- (n))))) 1))
					     (n (* 2 (n))))
		        (:instance int-quot (j (n)))))))

(defthmd quotf-error-b
  (implies (not (specialp))
           (< (abs (- (qsqrt (x) (1+ (* 2 (n))))
	              (quotf)))
	      (expt 2 (- (* 2 (n))))))
  :hints (("Goal" :in-theory (enable expt n)
                  :use (fnum-vals error-4 error-6 error-14 x-bounds
		        (:instance exactp-cmp-qsqrt (x (x)) (n (1+ (* 2 (n)))) (q (- (quotf) (expt 4 (- (n))))))
		        (:instance exactp-cmp-qsqrt (x (x)) (n (1+ (* 2 (n)))) (q (+ (quotf) (expt 4 (- (n))))))))))

(defthmd qsqrt-x-upper
  (implies (not (specialp))
           (< (qsqrt (x) (1+ (* 2 (n))))
	      (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (fnum-vals error-9 x-bounds
                        (:instance exactp-cmp-qsqrt (x (x)) (n (1+ (* 2 (n)))) (q (- 1 (expt 2 (- (1+ (p))))))))
		  :in-theory (enable n p prec f dp sp hp))))

(local-defthmd quotf-upper-1
  (implies (and (not (specialp))
                (= (* 2 (n)) (1+ (p))))
	   (< (quotf) 1))
  :hints (("Goal" :use (p-vals qsqrt-x-upper quotf-error-b)
		  :in-theory (enable n))))

(local-defthmd quotf-upper-2
  (implies (and (not (specialp))
                (= (* 2 (n)) (1+ (p))))
	   (<= (* (expt 2 (* 2 (n))) (quotf))
	       (1- (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (p-vals quotf-upper-1 (:instance int-quot (j (n))))
		  :in-theory (enable quotf n))))

(local-defthmd quotf-upper-3
  (implies (and (not (specialp))
                (= (* 2 (n)) (1+ (p))))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (p-vals quotf-upper-2)
                  :nonlinearp t
		  :in-theory (enable n))))

(local-defthmd quotf-upper-4
  (implies (and (not (specialp))
                (= (* 2 (n)) (+ 2 (p))))
	   (< (quotf) (- 1 (expt 2 (- (+ 2 (p)))))))
  :hints (("Goal" :use (p-vals qsqrt-x-upper quotf-error-b)
		  :in-theory (enable n))))

(local-defthmd quotf-upper-5
  (implies (and (not (specialp))
                (= (* 2 (n)) (+ 2 (p))))
	   (<= (* (expt 2 (* 2 (n))) (quotf))
	       (- (expt 2 (* 2 (n))) 2)))
  :hints (("Goal" :use (p-vals quotf-upper-4 (:instance int-quot (j (n))))
                  :nonlinearp t
		  :in-theory (enable quotf n))))

(local-defthmd quotf-upper-6
  (implies (and (not (specialp))
                (= (* 2 (n)) (+ 2 (p))))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (p-vals quotf-upper-5)
                  :nonlinearp t
		  :in-theory (enable quotf n))))

(defthmd quotf-upper
  (implies (not (specialp))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (quotf-upper-3 quotf-upper-6 fnum-vals)
		  :in-theory (enable n f dp sp hp p prec))))

(local-defund remsign ()
  (bitn (bits (+ (+ (rp-n) (lognot (rn-n))) 1) 58 0) 58))

(local-defund remzero () (log= (logxor (rp-n) (rn-n)) 0))

(local-defund cin () (lognot1 (remsign)))

(local-defund lsbis2 () (log= (true$) (log= (fnum) 1)))

(local-defund inc () (bits (if1 (lsbis2) 4 2) 2 0))

(local-defund q0 () (bits (+ (qp-shft) (lognot (qn-shft))) 53 0))

(local-defund qn1inc ()
  (bits (logxor (logxor (qp-shft) (bits (lognot (qn-shft)) 53 0))
                (inc))
        53 0))

(local-defund qp1inc ()
  (bits (ash (logior (logand (qp-shft) (bits (lognot (qn-shft)) 53 0))
                     (logand (logior (qp-shft) (bits (lognot (qn-shft)) 53 0))
                             (inc)))
             1)
        53 0))

(local-defund q1inc () (bits (+ (+ (qp1inc) (qn1inc)) 1) 53 0))

(local-defund q1low ()
  (bits (+ (+ (bits (qp-shft) 2 0) (lognot (bits (qn-shft) 2 0))) 1)
        2 0))

(local-defund q0inclow ()
  (bits (+ (bits (qp1inc) 2 0) (bits (qn1inc) 2 0))
        2 0))

(local-defund q1* ()
  (if1 (log= (q1low) 0)
       (setbits (q1low) 54 53 3 (bits (q1inc) 53 3))
       (setbits (q1low) 54 53 3 (bits (q0) 53 3))))

(local-defund q0inc ()
  (if1 (logior1 (log<= (q0inclow) 1) (logand1 (log<= (q0inclow) 3) (lsbis2)))
       (setbits (q0inclow) 54 53 3 (bits (q1inc) 53 3))
       (setbits (q0inclow) 54 53 3 (bits (q0) 53 3))))

(local-defund q01 () (bits (if1 (cin) (q1*) (q0)) 53 0))

(local-defund q01inc () (bits (if1 (cin) (q1inc) (q0inc)) 53 0))

(local-defund qtrunc* ()
  (bits (if1 (lsbis2) (ash (q01) (- 1)) (q01)) 52 0))

(local-defund qinc* ()
  (bits (if1 (lsbis2) (ash (q01inc) (- 1)) (q01inc)) 52 0))

(local-defund stk* () (lognot1 (remzero)))

(local-defthmd computeq-lemma
  (and (equal (qtrunc) (qtrunc*))
       (equal (qinc) (qinc*))
       (equal (stk) (stk*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(remsign remzero cin lsbis2 inc q0 qn1inc qp1inc q1inc q1low q0inclow q1* q0inc q01
		               q01inc qtrunc* qinc* stk* qtrunc qinc stk computeq))))

(local-defund qpf () (qp-shft))

(local-defund qnf () (qn-shft))

(local-defund rpf () (rp (n)))

(local-defund rnf () (rn (n)))

(local-in-theory (disable (remsign) (remzero) (cin) (lsbis2) (inc) (q0) (qn1inc) (qp1inc) (q1inc) (q1low) (q0inclow) (q1*)
                    (q0inc) (q01) (q01inc) (qtrunc*) (qinc*) (stk*) (qtrunc) (qinc) (stk) (computeq) (qpf) (qnf) (rpf) (rnf)))

(defthm integerp-qinc
  (integerp (qinc))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable computeq-lemma qinc*))))

(local-defthmd bvecp-qp
  (implies (and (not (specialp))
                (not (zp j)))
	   (bvecp (qp j) 54))
  :hints (("Goal" :induct (quot j) :in-theory (enable quot nextroot qp qp-1))))

(local-defthmd bvecp-qn
  (implies (and (not (specialp))
                (not (zp j)))
	   (bvecp (qn j) 54))
  :hints (("Goal" :induct (quot j) :in-theory (enable firstiter quot nextroot qn qn-1))))

(local-defthmd bvecp-qpf-qnf
  (implies (not (specialp))
           (and (bvecp (qpf) (* 2 (n)))
	        (bvecp (qnf) (* 2 (n)))))
  :hints (("Goal" :use ((:instance bvecp-qp (j (n)))
                        (:instance bvecp-qn (j (n)))
                        fnum-vals)
                  :in-theory (enable n qpf qnf qp-shft qn-shft))))

(local-defthmd bvecp-rp-j
  (bvecp (rp j) 59)
  :hints (("Goal" :expand ((rp j)) :use (fnum-vals) :in-theory (enable rp-1 firstiter nextrem))))

(local-defthm bvecp-rn-j
  (bvecp (rn j) 59)
  :hints (("Goal" :expand ((rn j)) :use (fnum-vals) :in-theory (enable rn-1 firstiter nextrem))))

(local-defthmd bvecp-rpf-rnf
  (implies (not (specialp))
           (and (bvecp (rpf) 59)
	        (bvecp (rnf) 59)))
  :hints (("Goal" :use ((:instance bvecp-rp-j (j (n))))
                  :in-theory (enable rpf rnf))))

(local-defthmd q0-rewrite
  (implies (not (specialp))
           (equal (q0) (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :in-theory (enable lognot n q0 bits qpf qnf)
                  :use (bvecp-qpf-qnf))))

(local-defthmd qn1inc-rewrite-1
  (implies (not (specialp))
           (equal (qn1inc)
	          (bits (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                (inc))
                        53 0)))
  :hints (("Goal" :in-theory (enable n qn1inc bits-logxor qpf qnf)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd qn1inc-rewrite-2
  (implies (not (specialp))
           (equal (qn1inc)
	          (mod (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                (inc))
                       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits qn1inc-rewrite-1))))

(local-defthmd qp1inc-rewrite-1
  (implies (not (specialp))
           (equal (qp1inc)
                  (* 2 (bits (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                     (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                             (inc)))
			     52 0))))
  :hints (("Goal" :in-theory (enable ash n qp1inc bits-logand bits-logior qpf qnf)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance bits-shift-up-2 (x (logior (logand (qp-shft) (bits (lognot (qn-shft)) 53 0))
                                                              (logand (logior (qp-shft) (bits (lognot (qn-shft)) 53 0))
                                                                      (inc))))
			                           (k 1)
						   (i 52))))))

(local-defthmd qp1inc-rewrite-2
  (implies (not (specialp))
           (equal (qp1inc)
                  (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                    (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                            (inc))))
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits qp1inc-rewrite-1)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance bits-shift-up-2 (x (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                                              (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                                      (inc))))
			                           (k 1)
						   (i 52))))))

(local-defthmd q1inc-rewrite-1
  (implies (not (specialp))
           (equal (q1inc)
                  (mod (+ (mod (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                       (inc))
                               (expt 2 54))
		          (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                            (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                    (inc))))
  		               (expt 2 54))
			  1)
		        (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q1inc qn1inc-rewrite-2 qp1inc-rewrite-2)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1inc-rewrite-2
  (implies (not (specialp))
           (equal (q1inc)
                  (mod (+ (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                  (inc))
		          (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                            (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                    (inc))))
  		               (expt 2 54))
			  1)
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bvecp q1inc-rewrite-1)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance mod-sum (a (1+ (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                                                    (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                                            (inc))))
  		                                       (expt 2 54))))
					   (b (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                                      (inc)))
					   (n (expt 2 54)))))))

(local-defthmd q1inc-rewrite-3
  (implies (not (specialp))
           (equal (q1inc)
                  (mod (+ (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                  (inc))
		          (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                       (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                               (inc))))
			  1)
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bvecp q1inc-rewrite-2)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance mod-sum (b (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                                           (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                                   (inc)))))
					   (a (1+ (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                                          (inc))))
					   (n (expt 2 54)))))))

(local-defthmd q1inc-rewrite-4
  (implies (not (specialp))
           (equal (+ (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                             (inc))
		     (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                  (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                          (inc))))
		     1)
		  (+ (qpf) (bits (lognot (qnf)) 53 0) (inc) 1)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance add-3 (x (qpf)) (y (bits (lognot (qnf)) 53 0)) (z (inc)))
			(:instance logior-logand-2 (y (qpf)) (z (bits (lognot (qnf)) 53 0)) (x (inc)))))))

(local-defthmd q1inc-rewrite-5
  (implies (not (specialp))
           (equal (q1inc)
                  (mod (+ (qpf) (bits (lognot (qnf)) 53 0) (inc) 1)
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bvecp q1inc-rewrite-3)
                  :use (fnum-vals bvecp-qpf-qnf q1inc-rewrite-4))))

(local-defthmd q1inc-rewrite-6
  (implies (not (specialp))
           (equal (q1inc)
                  (mod (+ (qpf) (expt 2 54) (- (qnf)) (inc))
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable n bvecp bits-lognot q1inc-rewrite-5)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1inc-rewrite-7
  (implies (not (specialp))
           (equal (q1inc)
                  (mod (+ (qpf) (- (qnf)) (inc))
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable n bvecp q1inc-rewrite-6)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance mod-mult (m (+ (qpf) (- (qnf)) (inc))) (a 1) (n (expt 2 54)))))))

(local-defthmd q1-rewrite-1
  (implies (not (specialp))
           (equal (q1low)
                  (mod (- (mod (qpf) 8) (mod (qnf) 8)) 8)))
  :hints (("Goal" :in-theory (enable bits lognot q1low qpf qnf)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1-rewrite-2
  (implies (not (specialp))
           (equal (q1low)
                  (mod (- (qpf) (qnf)) 8)))
  :hints (("Goal" :in-theory (enable q1-rewrite-1 n bvecp)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance mod-sum (a (- (mod (qnf) 8))) (b (qpf)) (n 8))
			(:instance mod-diff (a (qpf)) (b (qnf)) (n 8))))))

(local-defthm integerp-qpf
  (implies (not (specialp))
	   (integerp (qpf)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable n) :use (fnum-vals bvecp-qpf-qnf))))

(local-defthm integerp-qnf
  (implies (not (specialp))
	   (integerp (qnf)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable n) :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1-rewrite-3
  (implies (not (specialp))
           (equal (bits (q1*) 2 0) (mod (- (qpf) (qnf)) 8)))
  :hints (("Goal" :in-theory (enable q1* q1-rewrite-2 bvecp))))

(local-defthmd q1-rewrite-4
  (implies (not (specialp))
           (equal (mod (q1*) 8) (mod (- (qpf) (qnf)) 8)))
  :hints (("Goal" :in-theory (enable bits) :use (q1-rewrite-3))))

(local-defthmd z-k-n-1
  (implies (and (integerp z)
                (integerp k)
                (integerp n)
		(< 0 k)
		(<= k n))
	   (equal (fl (/ (+ z k) n))
	          (if (< (/ (+ z k) n) (1+ (fl (/ z n))))
		      (fl (/ z n))
		    (1+ (fl (/ z n))))))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd z-k-n-2
  (implies (and (integerp z)
                (integerp k)
                (integerp n)
		(< 0 k)
		(<= k n))
	   (equal (fl (/ (+ z k) n))
	          (if (>= (mod (+ z k) n) k)
		      (fl (/ z n))
		    (1+ (fl (/ z n))))))
  :hints (("Goal" :use (z-k-n-1
                        (:instance mod-def (x z) (y n))
                        (:instance mod-def (x (+ z k)) (y n))))))

(local-defthmd z-k-l-n
  (implies (and (integerp z)
                (integerp k)
                (integerp l)
                (integerp n)
		(< 0 k)
		(<= k l)
		(<= l n))
	   (equal (fl (/ (+ z k) n))
	          (if (>= (mod (+ z k) n) k)
		      (fl (/ z n))
		    (fl (/ (+ z l) n)))))
  :hints (("Goal" :nonlinearp t
                  :use (z-k-n-1 z-k-n-2
                        (:instance z-k-n-2 (k l))))))

(local-defthmd q1-rewrite-5
  (implies (and (not (specialp))
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (fl (/ (- (qpf) (qnf)) 8))
	          (fl (/ (+ (- (qpf) (qnf)) (inc)) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k 1) (l (1+ (inc))) (n 8))))))

(local-defthmd q1-rewrite-6
  (implies (and (not (specialp))
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (q1inc) 53 3)))
  :hints (("Goal" :in-theory (enable q1-rewrite-2 q1*) :use ((:instance bits-mod-fl (x (q1*)) (i 54) (j 3))))))

(local-defthmd q1-rewrite-7
  (implies (and (not (specialp))
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (+ (qpf) (- (qnf)) (inc)) 53 3)))
  :hints (("Goal" :in-theory (enable q1inc-rewrite-7)
                  :use (q1-rewrite-6 (:instance mod-bits-equal (x (q1inc)) (y (+ (qpf) (- (qnf)) (inc))) (i 53) (j 3))))))

(local-defthmd q1-rewrite-8
  (implies (and (not (specialp))
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-5 q1-rewrite-7
                        (:instance bits-mod-fl (x (+ (qpf) (- (qnf)) (inc))) (i 54) (j 3))))))

(local-defthmd q1-rewrite-9
  (implies (and (not (specialp))
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (fl (/ (- (qpf) (qnf)) 8))
	          (fl (/ (1- (- (qpf) (qnf))) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k 1) (l (1+ (inc))) (n 8))))))

(local-defthmd q1-rewrite-10
  (implies (and (not (specialp))
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (q0) 53 3)))
  :hints (("Goal" :in-theory (enable q1-rewrite-2 q1*) :use ((:instance bits-mod-fl (x (q1*)) (i 54) (j 3))))))

(local-defthmd q1-rewrite-11
  (implies (and (not (specialp))
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (mod (1- (- (qpf) (qnf))) (expt 2 54)) (expt 2 54))
	          (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (1- (- (qpf) (qnf)))) (a 54) (b 54))))))

(local-defthmd q1-rewrite-12
  (implies (and (not (specialp))
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (1- (- (qpf) (qnf))) 53 3)))
  :hints (("Goal" :in-theory (enable q0-rewrite)
                  :use (q1-rewrite-10 q1-rewrite-11 (:instance mod-bits-equal (x (q0)) (y (1- (- (qpf) (qnf)))) (i 53) (j 3))))))

(local-defthmd q1-rewrite-13
  (implies (and (not (specialp))
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-9 q1-rewrite-12
                        (:instance bits-mod-fl (x (1- (- (qpf) (qnf)))) (i 54) (j 3))))))

(local-defthmd q1-rewrite-14
  (implies (not (specialp))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-8 q1-rewrite-13))))

(local-defthmd q1-rewrite-14
  (implies (not (specialp))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-8 q1-rewrite-13))))

(local-defthmd q1-rewrite-15
  (implies (not (specialp))
           (equal (mod (* 8 (fl (/ (q1*) 8))) (expt 2 54))
	          (mod (* 8 (fl (/ (- (qpf) (qnf)) 8))) (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-14
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (q1*) 8))))
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (- (qpf) (qnf)) 8))))))))

(local-defthmd q1-rewrite-16
  (implies (not (specialp))
           (equal (mod (q1*) (expt 2 54))
	          (mod (+ (mod (* 8 (fl (/ (- (qpf) (qnf)) 8))) (expt 2 54))
		          (mod (- (qpf) (qnf)) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-4 q1-rewrite-15
                        (:instance mod-def (x (q1*)) (y 8))
                        (:instance mod-sum (a (mod (q1*) 8)) (b (* 8 (fl (/ (q1*) 8)))) (n (expt 2 54)))))))


(local-defthmd q1-rewrite-17
  (implies (not (specialp))
           (equal (mod (q1*) (expt 2 54))
	          (mod (+ (* 8 (fl (/ (- (qpf) (qnf)) 8)))
		          (mod (- (qpf) (qnf)) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-16
                        (:instance mod-sum (a (mod (- (qpf) (qnf)) 8)) (b (* 8 (fl (/ (- (qpf) (qnf)) 8)))) (n (expt 2 54)))))))

(local-defthmd q1-rewrite-18
  (implies (not (specialp))
           (equal (+ (* 8 (fl (/ (- (qpf) (qnf)) 8)))
		     (mod (- (qpf) (qnf)) 8))
		  (- (qpf) (qnf))))
  :hints (("Goal" :use ((:instance mod-def (x (- (qpf) (qnf))) (y 8))))))

(local-defthmd q1-rewrite-19
  (implies (not (specialp))
           (equal (mod (q1*) (expt 2 54))
	          (mod (- (qpf) (qnf)) (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-17 q1-rewrite-18)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd qp1inc-rewrite-3
  (implies (not (specialp))
           (equal (qp1inc)
                  (bits (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                    (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                            (inc))))
		        53 0)))
  :hints (("Goal" :in-theory (enable qp1inc-rewrite-1)
                  :use ((:instance bits-shift-up-2 (x (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                                              (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                                      (inc))))
			                           (k 1)
						   (i 52))))))

(local-defthmd q0inc-rewrite-1
  (implies (not (specialp))
           (equal (q0inclow)
                  (bits (+ (bits (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                         (inc))
			         2 0)
		           (bits (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                              (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                      (inc))))
  		                 2 0))
		        2 0)))
  :hints (("Goal" :in-theory (enable q0inclow qn1inc-rewrite-1 qp1inc-rewrite-3))))

(local-defthmd q0inc-rewrite-2
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (mod (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                       (inc))
                               8)
		          (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                            (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                    (inc))))
  		               8))
		        8)))
  :hints (("Goal" :in-theory (enable bits q0inc-rewrite-1))))

(local-defthmd q0inc-rewrite-3
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                  (inc))
		          (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                            (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                    (inc))))
  		               8))
		        8)))
  :hints (("Goal" :in-theory (enable bvecp q0inc-rewrite-2)
                  :use ((:instance mod-sum (a (mod (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                                                (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                                        (inc))))
  		                                   8))
					   (b (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                                      (inc)))
					   (n 8))))))

(local-defthmd q0inc-rewrite-4
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                  (inc))
		          (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                       (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                               (inc)))))
		        8)))
  :hints (("Goal" :in-theory (enable bvecp q0inc-rewrite-3)
                  :use ((:instance mod-sum (a (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0)) (inc)))
					   (b (* 2 (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                                           (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                                                   (inc)))))
					   (n 8))))))

(local-defthmd q0inc-rewrite-5
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (bits (lognot (qnf)) 53 0) (inc))
		       8)))
  :hints (("Goal" :in-theory (enable bvecp q0inc-rewrite-4)
                  :use (q1inc-rewrite-4))))

(local-defthmd q0inc-rewrite-6
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (expt 2 54) (- (bits (qnf) 53 0)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable bits-lognot q0inc-rewrite-5))))

(local-defthmd q0inc-rewrite-7
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (expt 2 54) (- (mod (qnf) (expt 2 54))) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable bits q0inc-rewrite-6))))

(local-defthmd q0inc-rewrite-8
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (mod (qnf) (expt 2 54))) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-7)
                  :use ((:instance mod-mult (m (+ (qpf) (- (mod (qnf) (expt 2 54))))) (a (expt 2 51)) (n 8))))))

(local-defthmd q0inc-rewrite-9
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (mod (mod (qnf) (expt 2 54)) 8)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-8)
                  :use ((:instance mod-diff (a (+ (qpf) (inc) -1)) (b (mod (qnf) (expt 2 54))) (n 8))))))

(local-defthmd q0inc-rewrite-10
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (mod (qnf) 8)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-9)
                  :use ((:instance mod-of-mod-cor (x (qnf)) (a 54) (b 3))))))

(local-defthmd q0inc-rewrite-11
  (implies (not (specialp))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (qnf)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-10)
                  :use ((:instance mod-diff (a (+ (qpf) (inc) -1)) (b (qnf)) (n 8))))))

(local-defthmd q0inc-rewrite-12
  (implies (not (specialp))
           (equal (bits (q0inc) 2 0)
                  (bits (mod (+ (qpf) (- (qnf)) (inc) -1) 8) 2 0)))
  :hints (("Goal" :in-theory (enable q0inc q0inc-rewrite-11))))

(local-defthmd q0inc-rewrite-13
  (implies (not (specialp))
           (equal (mod (q0inc) 8)
                  (mod (+ (qpf) (- (qnf)) (inc) -1) 8)))
  :hints (("Goal" :use (q0inc-rewrite-12) :in-theory (enable bits))))

(local-defthmd q0inc-rewrite-14
  (implies (and (not (specialp))
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))
	          (fl (/ (+ (- (qpf) (qnf)) (inc)) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k (inc)) (l (1+ (inc))) (n 8))))))

(local-defthmd q0inc-rewrite-15
  (implies (and (not (specialp))
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (q1inc) 53 3)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-11 q0inc lsbis2 inc) :use ((:instance bits-mod-fl (x (q0inc)) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-16
  (implies (and (not (specialp))
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (+ (qpf) (- (qnf)) (inc)) 53 3)))
  :hints (("Goal" :in-theory (enable q1inc-rewrite-7)
                  :use (q0inc-rewrite-15 (:instance mod-bits-equal (x (q1inc)) (y (+ (qpf) (- (qnf)) (inc))) (i 53) (j 3))))))

(local-defthmd q0inc-rewrite-17
  (implies (and (not (specialp))
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (mod (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)) (expt 2 51))))
  :hints (("Goal" :use (q0inc-rewrite-14 q0inc-rewrite-16
                        (:instance bits-mod-fl (x (+ (qpf) (- (qnf)) (inc))) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-18
  (implies (and (not (specialp))
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))
	          (fl (/ (1- (- (qpf) (qnf))) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k (inc)) (l (1+ (inc))) (n 8))))))

(local-defthmd q0inc-rewrite-19
  (implies (and (not (specialp))
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (q0) 53 3)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-11 q0inc lsbis2 inc) :use ((:instance bits-mod-fl (x (q0inc)) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-20
  (implies (and (not (specialp))
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (mod (1- (- (qpf) (qnf))) (expt 2 54)) (expt 2 54))
	          (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (1- (- (qpf) (qnf)))) (a 54) (b 54))))))

(local-defthmd q0inc-rewrite-21
  (implies (and (not (specialp))
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (1- (- (qpf) (qnf))) 53 3)))
  :hints (("Goal" :in-theory (enable q0-rewrite)
                  :use (q0inc-rewrite-19 q0inc-rewrite-20 (:instance mod-bits-equal (x (q0)) (y (1- (- (qpf) (qnf)))) (i 53) (j 3))))))

(local-defthmd q0inc-rewrite-22
  (implies (and (not (specialp))
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (mod (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)) (expt 2 51))))
  :hints (("Goal" :use (q0inc-rewrite-21 q0inc-rewrite-18
                        (:instance bits-mod-fl (x (1- (- (qpf) (qnf)))) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-23
  (implies (not (specialp))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (mod (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)) (expt 2 51))))
  :hints (("Goal" :use (q0inc-rewrite-22 q0inc-rewrite-17))))

(local-defthmd q0inc-rewrite-24
  (implies (not (specialp))
           (equal (mod (* 8 (fl (/ (q0inc) 8))) (expt 2 54))
	          (mod (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))) (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-23
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (q0inc) 8))))
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))))))))

(local-defthmd q0inc-rewrite-25
  (implies (not (specialp))
           (equal (mod (q0inc) (expt 2 54))
	          (mod (+ (mod (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))) (expt 2 54))
		          (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-13 q0inc-rewrite-24
                        (:instance mod-def (x (q0inc)) (y 8))
                        (:instance mod-sum (a (mod (q0inc) 8)) (b (* 8 (fl (/ (q0inc) 8)))) (n (expt 2 54)))))))


(local-defthmd q0inc-rewrite-26
  (implies (not (specialp))
           (equal (mod (q0inc) (expt 2 54))
	          (mod (+ (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)))
		          (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-25
                        (:instance mod-sum (a (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
			                   (b (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))))
					   (n (expt 2 54)))))))

(local-defthmd q0inc-rewrite-27
  (implies (not (specialp))
           (equal (+ (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)))
		     (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
		  (+ (- (qpf) (qnf)) (inc) -1)))
  :hints (("Goal" :use ((:instance mod-def (x (+ (- (qpf) (qnf)) (inc) -1)) (y 8))))))

(local-defthmd q0inc-rewrite-28
  (implies (not (specialp))
           (equal (mod (q0inc) (expt 2 54))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-26 q0inc-rewrite-27)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd r-rp-rn
  (implies (not (specialp))
	   (equal (mod (* (expt 2 55) (rf)) (expt 2 59))
	          (mod (- (rpf) (rnf)) (expt 2 59))))
  :hints (("Goal" :use (fnum-vals (:instance inv-lemma (j (n))))
                  :in-theory (enable n rf rpf rnf inv rpn-inv))))

(local-defthmd r-bound
  (implies (and (not (specialp))
                (not (zp j))
		(inv j))
           (< (abs (* (expt 2 55) (r j)))
              (expt 2 56)))
  :hints (("Goal" :in-theory (enable inv r-bnds-inv blo bhi quot-bnds-inv)
                  :nonlinearp t)))

(local-defthmd rf-bound
  (implies (not (specialp))
           (< (abs (* (expt 2 55) (rf))) (expt 2 56)))
  :hints (("Goal" :use (fnum-vals (:instance inv-lemma (j (n))) (:instance r-bound (j (n))))
                  :in-theory (enable n rf))))

(local-defthmd r-rp-rn-0
  (implies (not (specialp))
	   (iff (= (rf) 0)
	        (= (rpf) (rnf))))
  :hints (("Goal" :use (r-rp-rn bvecp-rpf-rnf rf-bound
                        (:instance mod-force-equal (a (* (expt 2 55) (rf))) (b 0) (n (expt 2 59)))
                        (:instance mod-force-equal (a (- (rpf) (rnf))) (b 0) (n (expt 2 59))))
		  :in-theory (enable bvecp))))

(local-defthmd remzero-rewrite-1
  (implies (not (specialp))
           (equal (remzero)
	          (if (= (logxor (rpf) (rnf)) 0) 1 0)))
  :hints (("Goal" :in-theory (enable remzero rpf rnf))))

(local-defthm integerp-rpf
  (implies (not (specialp))
	   (integerp (rpf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthm integerp-rnf
  (implies (not (specialp))
	   (integerp (rnf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd remzero-rewrite-2
  (implies (not (specialp))
	   (equal (remzero)
	          (if (= (rf) 0) 1 0)))
  :hints (("Goal" :use (r-rp-rn-0
                        (:instance logxor-not-0 (x (rpf)) (y (rnf))))
		  :in-theory (enable remzero-rewrite-1))))

(local-defthmd remsign-rewrite-1
  (implies (not (specialp))
           (equal (remsign)
                  (bitn (bits (- (rpf) (rnf)) 58 0) 58)))
  :hints (("Goal" :use (bvecp-rpf-rnf) :in-theory (enable lognot rpf rnf remsign))))

(local-defthmd remsign-rewrite-2
  (implies (not (specialp))
           (equal (remsign)
                  (bitn (bits (* (expt 2 55) (rf)) 58 0) 58)))
  :hints (("Goal" :use (r-rp-rn) :in-theory (enable remsign-rewrite-1 bits))))

(local-defthmd remsign-rewrite-3
  (implies (not (specialp))
           (equal (remsign)
                  (if (< (si (bits (* (expt 2 55) (rf)) 58 0) 59) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable si remsign-rewrite-2)
                  :use ((:instance bits-bounds (x (* (expt 2 55) (rf))) (i 58) (j 0))))))

(local-defthmd int-rf
  (implies (not (specialp))
           (integerp (* (expt 2 55) (rf))))
  :hints (("Goal" :in-theory (enable rf n inv rpn-inv)
                  :use (fnum-vals (:instance inv-lemma (j (n)))))))

(local-defthmd remsign-rewrite-4
  (implies (not (specialp))
           (equal (remsign)
                  (if (< (rf) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable remsign-rewrite-3)
                  :nonlinearp t
                  :use (rf-bound int-rf (:instance si-bits (x (* (expt 2 55) (rf))) (n 59))))))

(local-defthmd remsign-rewrite-5
  (implies (not (specialp))
           (<= (expo (quotf)) -1))
  :hints (("Goal" :use (p-vals quotf-upper (:instance expo<= (x (quotf)) (n -1))))))

(local-defthmd remsign-rewrite-6
  (implies (not (specialp))
           (exactp (quotf) (* 2 (n))))
  :hints (("Goal" :in-theory (enable quotf exactp2 n)
                  :use (fnum-vals remsign-rewrite-5
		        (:instance exactp-<= (x (quotf))
			                     (m (+ (* 2 (n)) (expo (quotf)) 1))
					     (n (* 2 (n))))
		        (:instance int-quot (j (n)))))))

(local-defthmd remsign-rewrite
  (implies (not (specialp))
           (equal (remsign)
                  (if (< (qsqrt (x) (1+ (* 2 (n))))
                         (quotf))
		      1 0)))
  :hints (("Goal" :in-theory (enable remsign-rewrite-4 quotf rf r n)
                  :nonlinearp t
                  :use (fnum-vals remsign-rewrite-6 quotf-bounds
                        (:instance exactp-cmp-qsqrt (n (1+ (* 2 (n)))) (q (quotf)) (x (x)))))))

(local-defthmd remzero-rewrite
  (implies (not (specialp))
           (equal (remzero)
                  (if (= (qsqrt (x) (1+ (* 2 (n))))
                         (quotf))
		      1 0)))
  :hints (("Goal" :in-theory (enable remzero-rewrite-2 quotf rf r n)
                  :nonlinearp t
                  :use (fnum-vals remsign-rewrite-6 quotf-bounds
                        (:instance exactp-cmp-qsqrt (n (1+ (* 2 (n)))) (q (quotf)) (x (x)))))))

(local-defthmd quot-1
  (implies (not (specialp))
           (< (abs (- (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
	              (* (expt 2 (* 2 (n))) (quotf))))
	      1))
  :hints (("Goal" :use (quotf-error-b) :nonlinearp t)))

(local-defthmd quot-2
  (implies (and (not (specialp))
                (= (remsign) 0))
           (and (>= (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
	            (* (expt 2 (* 2 (n))) (quotf)))
		(< (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
	           (1+ (* (expt 2 (* 2 (n))) (quotf))))))
  :hints (("Goal" :use (quot-1) :in-theory (enable remsign-rewrite) :nonlinearp t)))

(local-defthmd quot-3
  (implies (not (specialp))
           (integerp (* (expt 2 (* 2 (n))) (quotf))))
  :hints (("Goal" :use (fnum-vals (:instance int-quot (j (n))))
                  :in-theory (enable n quotf))))

(local-defthmd quot-4
  (implies (and (not (specialp))
                (= (remsign) 0))
	   (equal (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
	          (* (expt 2 (* 2 (n))) (quotf))))
  :hints (("Goal" :use (quot-2 quot-3
                        (:instance fl-unique (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
			                     (n (* (expt 2 (* 2 (n))) (quotf))))))))

(local-defthmd quot-5
  (implies (and (not (specialp))
                (= (remsign) 0))
	   (equal (cin) 1))
  :hints (("Goal" :in-theory (enable cin remsign-rewrite))))

(local-defthmd quot-6
  (implies (and (not (specialp))
                (= (remsign) 0))
           (equal (mod (q01) (expt 2 54))
	          (mod (- (qpf) (qnf)) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q01 quot-5)
                  :use (q1-rewrite-19))))

(local-defthmd quot-7
  (implies (and (not (specialp))
                (= (remsign) 0))
           (equal (mod (q01) (expt 2 (* 2 (n))))
	          (mod (- (qpf) (qnf)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-6
                        (:instance mod-of-mod-cor (x (q01)) (a 54) (b (* 2 (n))))
                        (:instance mod-of-mod-cor (x (- (qpf) (qnf))) (a 54) (b (* 2 (n))))))))

(local-defthmd quot-8
  (implies (not (specialp))
	   (equal (* (expt 2 (* 2 (n))) (1- (quotf)))
	          (- (qpf) (qnf))))
  :hints (("Goal" :in-theory (enable qp-shft qn-shft qpn-inv inv qpf qnf quotf n)
                  :use (fnum-vals
		        (:instance bvecp-qp (j (n)))
		        (:instance bvecp-qn (j (n)))
		        (:instance bits-plus-bits (x (qp (n))) (n 53) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (qn (n))) (n 53) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance inv-lemma (j (n)))))))

(local-defthmd quot-9
  (implies (not (specialp))
	   (equal (mod (* (expt 2 (* 2 (n))) (1- (quotf))) (expt 2 (* 2 (n))))
	          (mod (- (qpf) (qnf)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-8) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-10
  (implies (not (specialp))
	   (equal (mod (* (expt 2 (* 2 (n))) (quotf)) (expt 2 (* 2 (n))))
	          (mod (- (qpf) (qnf)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-9 (:instance mod-mult (m (* (expt 2 (* 2 (n))) (quotf))) (a -1) (n (expt 2 (* 2 (n)))))))))

(local-defthmd quot-11
  (implies (and (not (specialp))
                (= (remsign) 0))
           (equal (mod (q01) (expt 2 (* 2 (n))))
	          (mod (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-4 quot-7 quot-10))))

(local-defthmd quot-12
  (implies (and (not (specialp))
                (= (remsign) 0))
           (equal (mod (q01inc) (expt 2 54))
	          (mod (+ (- (qpf) (qnf)) (inc)) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q01inc quot-5)
                  :use (q1inc-rewrite-7))))

(local-defthmd quot-13
  (implies (and (not (specialp))
                (= (remsign) 0))
           (equal (mod (q01inc) (expt 2 (* 2 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-12
                        (:instance mod-of-mod-cor (x (q01inc)) (a 54) (b (* 2 (n))))
                        (:instance mod-of-mod-cor (x (+ (- (qpf) (qnf)) (inc))) (a 54) (b (* 2 (n))))))))

(local-defthmd quot-14
  (implies (not (specialp))
	   (equal (+ (inc) (* (expt 2 (* 2 (n))) (1- (quotf))))
	          (+ (- (qpf) (qnf)) (inc))))
  :hints (("Goal" :use (quot-8))))

(local-defthmd quot-15
  (implies (not (specialp))
	   (equal (mod (+ (inc) (* (expt 2 (* 2 (n))) (1- (quotf)))) (expt 2 (* 2 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-14) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-16
  (implies (not (specialp))
	   (equal (mod (+ (* (expt 2 (* 2 (n))) (quotf)) (inc)) (expt 2 (* 2 (n))))
	          (mod (+ (inc) (* (expt 2 (* 2 (n))) (1- (quotf)))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use ((:instance mod-mult (m (+ (* (expt 2 (* 2 (n))) (quotf)) (inc))) (a -1) (n (expt 2 (* 2 (n)))))))))

(local-defthmd quot-17
  (implies (and (not (specialp))
                (= (remsign) 0))
           (equal (mod (q01inc) (expt 2 (* 2 (n))))
	          (mod (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (inc)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-4 quot-13 quot-15 quot-16))))

(local-defthmd quot-2-1
  (implies (and (not (specialp))
                (= (remsign) 1))
           (and (< (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
	            (* (expt 2 (* 2 (n))) (quotf)))
		(> (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
	           (1- (* (expt 2 (* 2 (n))) (quotf))))))
  :hints (("Goal" :use (quot-1) :in-theory (enable remsign-rewrite) :nonlinearp t)))

(local-defthmd quot-18
  (implies (and (not (specialp))
                (= (remsign) 1))
	   (equal (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
	          (1- (* (expt 2 (* 2 (n))) (quotf))))	          )
  :hints (("Goal" :use (quot-2-1 quot-3
                        (:instance fl-unique (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (n (1- (* (expt 2 (* 2 (n))) (quotf)))))))))

(local-defthmd quot-19
  (implies (and (not (specialp))
                (= (remsign) 1))
	   (equal (cin) 0))
  :hints (("Goal" :in-theory (enable cin remsign-rewrite))))

(in-theory (disable ACL2::|(mod (- x) y)|))

(local-defthmd quot-20
  (implies (and (not (specialp))
                (= (remsign) 1))
           (equal (mod (q01) (expt 2 54))
	          (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q0-rewrite q01 quot-19)
                  :use ((:instance mod-of-mod-cor (x (q0)) (a 54) (b 54))))))

(local-defthmd quot-21
  (implies (and (not (specialp))
                (= (remsign) 1))
           (equal (mod (q01) (expt 2 (* 2 (n))))
	          (mod (1- (- (qpf) (qnf))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-20
                        (:instance mod-of-mod-cor (x (q01)) (a 54) (b (* 2 (n))))
                        (:instance mod-of-mod-cor (x (1- (- (qpf) (qnf)))) (a 54) (b (* 2 (n))))))))

(local-defthmd quot-22
  (implies (not (specialp))
	   (equal (1- (* (expt 2 (* 2 (n))) (1- (quotf))))
	          (1- (- (qpf) (qnf)))))
  :hints (("Goal" :use (quot-8))))

(local-defthmd quot-23
  (implies (not (specialp))
	   (equal (mod (1- (* (expt 2 (* 2 (n))) (1- (quotf)))) (expt 2 (* 2 (n))))
	          (mod (1- (- (qpf) (qnf))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-22) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-24
  (implies (not (specialp))
	   (equal (mod (1- (* (expt 2 (* 2 (n))) (1- (quotf)))) (expt 2 (* 2 (n))))
	          (mod (1- (* (expt 2 (* 2 (n))) (quotf))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use ((:instance mod-mult (m (1- (* (expt 2 (* 2 (n))) (quotf)))) (a -1) (n (expt 2 (* 2 (n)))))))))

(local-defthmd quot-25
  (implies (and (not (specialp))
                (= (remsign) 1))
           (equal (mod (q01) (expt 2 (* 2 (n))))
	          (mod (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-18 quot-21 quot-23 quot-24))))

(local-defthmd quot-26
  (implies (and (not (specialp))
                (= (remsign) 1))
           (equal (mod (q01inc) (expt 2 54))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q01inc quot-19)
                  :use (q0inc-rewrite-28 (:instance mod-of-mod-cor (x (q0inc)) (a 54) (b 54))))))

(local-defthmd quot-27
  (implies (and (not (specialp))
                (= (remsign) 1))
           (equal (mod (q01inc) (expt 2 (* 2 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-26
                        (:instance mod-of-mod-cor (x (q01inc)) (a 54) (b (* 2 (n))))
                        (:instance mod-of-mod-cor (x (+ (- (qpf) (qnf)) (inc) -1)) (a 54) (b (* 2 (n))))))))

(local-defthmd quot-28
  (implies (not (specialp))
	   (equal (+ (* (expt 2 (* 2 (n))) (1- (quotf))) (inc) -1)
	          (+ (- (qpf) (qnf)) (inc) -1)))
  :hints (("Goal" :use (quot-8))))

(local-defthmd quot-29
  (implies (not (specialp))
	   (equal (mod (+ (* (expt 2 (* 2 (n))) (1- (quotf))) (inc) -1) (expt 2 (* 2 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-28) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-30
  (implies (not (specialp))
	   (equal (mod (+ (* (expt 2 (* 2 (n))) (1- (quotf))) (inc) -1) (expt 2 (* 2 (n))))
	          (mod (+ (* (expt 2 (* 2 (n))) (quotf)) (inc) -1) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use ((:instance mod-mult (m (+ (* (expt 2 (* 2 (n))) (quotf)) (inc) -1)) (a -1) (n (expt 2 (* 2 (n)))))))))

(local-defthmd quot-31
  (implies (and (not (specialp))
                (= (remsign) 1))
           (equal (mod (q01inc) (expt 2 (* 2 (n))))
	          (mod (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (inc)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (quot-18 quot-27 quot-29 quot-30))))

(local-defthmd quot-32
  (implies (not (specialp))
           (equal (mod (q01) (expt 2 (* 2 (n))))
	          (mod (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable remsign-rewrite) :use (quot-11 quot-25))))

(local-defthmd quot-33
  (implies (not (specialp))
           (equal (mod (q01inc) (expt 2 (* 2 (n))))
	          (mod (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (inc)) (expt 2 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable remsign-rewrite) :use (quot-17 quot-31))))

(local-defthmd qtrunc-rewrite-1
  (implies (and (not (specialp)) (not (= (fnum) 1)))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (p)))))
  :hints (("Goal" :use (quot-32 fnum-vals
                        (:instance mod-of-mod-cor (x (q01)) (a 53) (b (p)))
                        (:instance mod-of-mod-cor (x (q01)) (a (* 2 (n))) (b (p)))
                        (:instance mod-of-mod-cor (x (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
			                          (a (* 2 (n))) (b (p))))
                  :in-theory (enable ash-rewrite bits prec dp sp hp p f n computeq-lemma qtrunc* lsbis2))))

(local-defthmd qtrunc-rewrite-2
  (implies (and (not (specialp)) (= (fnum) 1))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (p)))))
  :hints (("Goal" :use (quot-32 fnum-vals
                        (:instance fl/int-rewrite (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (n 2))
                        (:instance mod-of-mod-cor (x (fl (/ (q01) 2))) (a 53) (b (p)))
                        (:instance mod-of-mod-cor (x (q01)) (a (* 2 (n))) (b (1+ (p))))
                        (:instance mod-of-mod-cor (x (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
			                          (a (* 2 (n))) (b (1+ (p))))
                        (:instance fl-mod (a (q01)) (n 2) (m (expt 2 (p))))
                        (:instance fl-mod (a (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
			                  (n 2) (m (expt 2 (p)))))
                  :in-theory (enable ash-rewrite bits prec dp sp hp p f n computeq-lemma qtrunc* lsbis2))))

(defthmd qtrunc-rewrite
  (implies (not (specialp))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-rewrite-1 qtrunc-rewrite-2))))

(local-defthmd qinc-rewrite-1
  (implies (and (not (specialp)) (not (= (fnum) 1)))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2) (expt 2 (p)))))
  :hints (("Goal" :use (quot-33 fnum-vals
                        (:instance mod-of-mod-cor (x (q01inc)) (a 53) (b (p)))
                        (:instance mod-of-mod-cor (x (q01inc)) (a (* 2 (n))) (b (p)))
                        (:instance mod-of-mod-cor (x (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) 2))
			                          (a (* 2 (n))) (b (p))))
                  :in-theory (enable ash-rewrite inc bits prec dp sp hp p f n computeq-lemma qinc* lsbis2))))

(local-defthmd qinc-rewrite-2
  (implies (and (not (specialp)) (= (fnum) 1))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (fl (+ 2 (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2))) (expt 2 (p)))))
  :hints (("Goal" :use (quot-33 fnum-vals
                        ;(:instance fl/int-rewrite (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (n 2))
                        (:instance mod-of-mod-cor (x (fl (/ (q01inc) 2))) (a 53) (b (p)))
                        (:instance mod-of-mod-cor (x (q01inc)) (a (* 2 (n))) (b (1+ (p))))
                        (:instance mod-of-mod-cor (x (+ 4 (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
			                          (a (* 2 (n))) (b (1+ (p))))
                        (:instance fl-mod (a (q01inc)) (n 2) (m (expt 2 (p))))
                        (:instance fl-mod (a (+ 4 (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
			                  (n 2) (m (expt 2 (p)))))
                  :in-theory (enable ash-rewrite inc bits prec dp sp hp p f n computeq-lemma qinc* lsbis2))))

(local-defthmd qinc-rewrite-3
  (implies (and (not (specialp)) (= (fnum) 1))
           (equal (fl (+ 2 (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2)))
	          (+ 2 (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))))
  :hints (("Goal" :use (fnum-vals
                        (:instance fl+int-rewrite (x (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2)) (n 2))
                        (:instance fl/int-rewrite (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (n 2)))
                  :in-theory (enable prec dp sp hp p f n))))

(defthmd qinc-rewrite
  (implies (not (specialp))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2) (expt 2 (p)))))
  :hints (("Goal" :use (qinc-rewrite-1 qinc-rewrite-2 qinc-rewrite-3))))

(local-defthmd stk-1
  (implies (not (specialp))
	   (equal (stk)
	          (if (= (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
		         (* (expt 2 (* 2 (n))) (quotf)))
		      0 1)))
  :hints (("Goal" :nonlinearp t :use (fnum-vals) :in-theory (enable n remzero-rewrite stk* computeq-lemma))))

(local-defthmd stk-2
  (implies (and (integerp n) (rationalp x) (< (abs (- x n)) 1))
           (iff (integerp x) (= x n))))

(local-defthmd stk-3
  (implies (not (specialp))
	   (equal (stk)
	          (if (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1)))
  :hints (("Goal" :in-theory (enable stk-1)
                  :use (quot-1 quot-3
		        (:instance stk-2 (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))) (n (* (expt 2 (* 2 (n))) (quotf))))))))

(local-defthmd stk-4
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2))))
	   (= (* 2 (n)) (+ 2 (p))))
  :hints (("Goal" :in-theory (enable prec p f dp sp hp n)
                  :use (fnum-vals))))

(local-defthmd stk-5
  (implies (and (not (specialp))
		(member (fnum) '(0 2)))
	   (equal (stk)
	          (if (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1)))
  :hints (("Goal" :in-theory (enable stk-3 prec p f dp sp hp n)
                  :use (fnum-vals))))

(local-defthmd stk-6
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2)))
		(integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
	   (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
  :hints (("Goal" :in-theory (enable prec p f dp sp hp n)
                  :use (fnum-vals))))

(local-defund s () (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n))))))

(local-in-theory (disable (s)))

(local-defthmd stk-7
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2)))
		(not (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
	        (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
	   (and (integerp (s)) (oddp (s))))
  :hints (("Goal" :in-theory (enable s) :use (stk-4))))

(local-defthm stk-8
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(local-defthmd stk-9
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2)))
	        (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
	   (exactp (qsqrt (x) (1+ (* 2 (n)))) (* 2 (n))))
  :hints (("Goal" :in-theory (enable n exactp2)
                  :use (fnum-vals qsqrt-x-upper p-vals
		        (:instance expo<= (x (qsqrt (x) (1+ (* 2 (n))))) (n -1))
			(:instance stk-8 (x (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
			                 (y (expt 2 (- (1+ (expo (qsqrt (x) (1+ (* 2 (n))))))))))))))

(local-defthmd stk-10
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2)))
	        (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
	   (equal (* (qsqrt (x) (1+ (* 2 (n))))
	             (qsqrt (x) (1+ (* 2 (n)))))
		  (x)))
  :hints (("Goal" :in-theory (enable n exactp2)
                  :use (fnum-vals stk-9 x-bounds
		        (:instance qsqrt-sqrt (x (x)) (n (1+ (* 2 (n)))))))))

(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))

(local-defthmd stk-11
  (implies (and (integerp a)
                (oddp a)
		(integerp b)
                (oddp b))
	   (oddp (* a b)))
  :hints (("Goal" :in-theory (enable divides) :use ((:instance euclid (p 2))))))

(local-defthmd stk-12
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2)))
		(not (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
	        (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
	   (oddp (* (expt 2 (+ 4 (* 2 (p)))) (x))))
  :hints (("Goal" :in-theory (enable s) :use (p-vals stk-7 stk-10 (:instance stk-11 (a (s)) (b (s)))))))

(local-defthmd stk-13
  (implies (not (specialp))
           (integerp (* (expt 2 (1+ (p))) (x))))
  :hints (("Goal" :use (p-vals exactp-a)
                  :in-theory (enable x))))

(local-defthmd stk-14
  (implies (not (specialp))
           (evenp (* (expt 2 (+ 4 (* 2 (p)))) (x))))
  :hints (("Goal" :use (p-vals stk-13))))

(local-defthmd stk-15
  (implies (and (not (specialp))
		(not (member (fnum) '(0 2)))
	        (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
	   (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
  :hints (("Goal" :use (stk-12 stk-14))))

(defthmd stk-rewrite
  (implies (not (specialp))
	   (equal (stk)
	          (if (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1)))
  :hints (("Goal" :use (stk-3 stk-5 stk-6 stk-15))))



