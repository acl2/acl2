(in-package "RTL")

(include-book "induct")

(local-defthmd quot-lower-1
  (implies (and (not (specialp))
                (not (zp j))
		(> (quot j) 1))
	   (> (* (expt 4 (1- j)) (quot j))
	      (expt 4 (1- j))))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd quot-lower-2
  (implies (and (not (specialp))
                (not (zp j))
		(> (quot j) 1))
	   (integerp (expt 4 (1- j)))))

(local-defthmd quot-lower-3
  (implies (and (integerp n) (integerp m) (> n m))
           (>= n (1+ m))))

(local-defthmd quot-lower-4
  (implies (and (not (specialp))
                (not (zp j))
		(> (quot j) 1))
	   (>= (* (expt 4 (1- j)) (quot j))
	       (1+ (expt 4 (1- j)))))
  :hints (("Goal" :use (int-quot quot-lower-1 quot-lower-2
                        (:instance quot-lower-3 (n (* (expt 4 (1- j)) (quot j))) (m (expt 4 (1- j))))))))

(local-defthmd quot-lower-5
  (implies (and (not (specialp))
                (not (zp j))
		(> (quot j) 1))
	   (>= (quot j) (1+ (expt 4 (- 1 j)))))
  :hints (("Goal" :use (quot-lower-4) :nonlinearp t)))

(local-defthmd quot-lower-6
  (implies (and (not (zp j))
		(not (zp k)))
	   (equal (* 4/3 (EXPT 2 (+ 3 (* -2 J) (* -2 K))))
	          (* 1/3 (EXPT 2 (+ 5 (* -2 J) (* -2 K)))))))

(local-defthmd quot-lower-7
  (implies (and (not (specialp))
                (not (zp j))
		(not (zp k))
		(>= (quot (+ j (1- k)))
		    (- (quot j) (* 1/3 (expt 2 (- 3 (* 2 j))) (- 1 (expt 4 (- (1- k))))))))
           (>= (quot (+ j k))
               (- (quot j) (* 1/3 (expt 2 (- 3 (* 2 j))) (- 1 (expt 4 (- k)))))))
  :hints (("Goal" :nonlinearp t :use (quot-lower-6 (:instance q-vals (j (+ j k)))) :expand ((quot (+ j k))))))

(defun natp-induct (k)
  (if (zp k)
      k
    (natp-induct (1- k))))

(local-defthmd quot-lower-8
  (implies (and (not (specialp))
                (not (zp j))
		(natp k))
           (>= (quot (+ j k))
               (- (quot j) (* 1/3 (expt 2 (- 3 (* 2 j))) (- 1 (expt 4 (- k)))))))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/2" :use (quot-lower-7))))

(local-defthmd quot-lower-9
  (implies (and (not (specialp))
                (not (zp j))
		(natp k))
           (> (quot (+ j k))
              (- (quot j) (* 1/3 (expt 2 (- 3 (* 2 j)))))))
  :hints (("Goal" :use (quot-lower-8))))

(local-defthmd quot-lower-10
  (implies (and (not (specialp))
                (not (zp j))
		(natp k)
		(>= (quot j) (1+ (expt 4 (- 1 j)))))
           (> (quot (+ j k)) 1))
  :hints (("Goal" :nonlinearp t :use (quot-lower-9))))

(local-defthmd quot-lower-11
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (1+ (* 3 (n))))
		(> (quot j) 1))
           (> (quotf) 1))
  :hints (("Goal" :in-theory (enable quotf)
                  :use (quot-lower-5 (:instance quot-lower-10 (k (- (1+ (* 3 (n))) j)))))))

(local-defthmd quot-lower-12
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (1+ (* 3 (n))))
		(= (quot j) 1))
           (>= (r j) 0))
  :hints (("Goal" :in-theory (enable r)
                  :use (x-bounds))))

(local-defthmd quot-lower-13
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n))))
	   (and (= (q (1+ j)) (maxk (approx (1+ j))))
                (< (abs (- (approx (1+ j)) (* 4 (r j)))) 1/8)))
  :hints (("Goal" :use ((:instance induction-result (j (1+ j)))))))

(local-defthmd quot-lower-14
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(= (quot j) 1))
           (> (approx (1+ j)) -1/8))
  :hints (("Goal" :nonlinearp t :use (quot-lower-12 quot-lower-13))))

(local-defthmd quot-lower-15
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(= (quot j) 1))
           (>= (q (1+ j)) 0))
  :hints (("Goal" :use (quot-lower-13 quot-lower-14)
                  :in-theory (enable m maxk))))

(local-defthmd quot-lower-16
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(= (quot j) 1))
           (>= (quot (1+ j)) 1))
  :hints (("Goal" :use (quot-lower-15)
                  :in-theory (enable quot))))

(local-defthmd quot-lower-17
  (implies (and (not (specialp))
                (natp k)
		(<= k (* 3 (n)))
		(>= (quot (- (1+ (* 3 (n))) k)) 1))
           (>= (quotf) 1))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/1" :in-theory (enable quotf))
          ("Subgoal *1/2" :in-theory (enable quotf)
	                  :use ((:instance quot-lower-16 (j (1+ (- (* 3 (n)) k))))
			        (:instance quot-lower-11 (j (1+ (- (* 3 (n)) k))))))))

(local-defthmd quot-lower
  (implies (not (specialp))
           (>= (quotf) 1))
  :hints (("Goal" :expand ((quot 0) (quot 1)) :use (q1-vals (:instance quot-lower-17 (k (* 3 (n))))))))

(local-defthmd quot-upper-1
  (implies (and (not (specialp))
                (not (zp j))
		(< (quot j) 2))
	   (< (* (expt 4 (1- j)) (quot j))
	      (* 2 (expt 4 (1- j)))))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd quot-upper-2
  (implies (and (not (specialp))
                (not (zp j))
		(< (quot j) 2))
	   (integerp (expt 4 (1- j)))))

(local-defthmd quot-upper-3
  (implies (and (integerp n) (integerp m) (< n m))
           (<= n (1- m))))

(local-defthmd quot-upper-4
  (implies (and (not (specialp))
                (not (zp j))
		(< (quot j) 2))
	   (<= (* (expt 4 (1- j)) (quot j))
	       (1- (* 2 (expt 4 (1- j))))))
  :hints (("Goal" :use (int-quot quot-upper-1 quot-upper-2
                        (:instance quot-upper-3 (n (* (expt 4 (1- j)) (quot j))) (m (* 2 (expt 4 (1- j)))))))))

(local-defthmd quot-upper-5
  (implies (and (not (specialp))
                (not (zp j))
		(< (quot j) 2))
	   (<= (quot j) (- 2 (expt 4 (- 1 j)))))
  :hints (("Goal" :use (quot-upper-4) :nonlinearp t)))

(local-defthmd quot-upper-6
  (implies (and (not (specialp))
                (not (zp j))
		(< (quot j) 2))
	   (< (quot (1+ j)) 2))
  :hints (("Goal" :expand ((quot (+ 1 j))) :use (quot-upper-5 (:instance q-vals (j (1+ j)))) :nonlinearp t)))

(local-defthmd quot-upper-7
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (1+ (* 3 (n))))
		(= (quot j) 2))
           (< (r j) 0))
  :hints (("Goal" :in-theory (enable r)
                  :use (x-bounds))))

(local-defthmd quot-upper-8
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n))))
	   (and (= (q (1+ j)) (maxk (approx (1+ j))))
                (< (abs (- (approx (1+ j)) (* 4 (r j)))) 1/8)))
  :hints (("Goal" :use ((:instance induction-result (j (1+ j)))))))

(local-defthmd quot-upper-9
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(= (quot j) 2))
           (< (approx (1+ j)) 1/8))
  :hints (("Goal" :nonlinearp t :use (quot-upper-7 quot-upper-8))))

(local-defthmd quot-upper-10
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(= (quot j) 2))
           (<= (q (1+ j)) 0))
  :hints (("Goal" :use (quot-upper-8 quot-upper-9)
                  :in-theory (enable m maxk))))

(local-defthmd quot-upper-11
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(= (quot j) 2))
           (<= (quot (1+ j)) 2))
  :hints (("Goal" :use (quot-upper-10)
                  :in-theory (enable quot))))

(local-defthmd quot-upper-12
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(<= (quot j) 2))
           (<= (quot (1+ j)) 2))
  :hints (("Goal" :use (quot-upper-11 quot-upper-6))))

(local-defthmd quot-upper-13
  (implies (and (not (specialp))
                (not (zp k))
		(<= k (* 3 (n))))
           (<= (quot k) 2))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/2" :expand ((quot 0) (quot 1)) :use (q1-vals))
          ("Subgoal *1/1" :expand ((quot 0) (quot 1)) :use (q1-vals (:instance quot-upper-12 (j (1- k)))))))

(local-defthmd quot-upper-14
  (implies (not (specialp))
           (<= (quot (* 3 (n))) 2))
  :hints (("Goal" :in-theory (enable quot n) :use ((:instance quot-upper-13 (k (* 3 (n))))))))

(local-defthmd quot-upper-15
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (< (quot (* 3 (n))) 2))
	   (< (quotf) 2))
  :hints (("Goal" :in-theory (enable quot n quotf)
                  :use (fnum-vals (:instance quot-upper-6 (j (* 3 (n))))))))

(local-defthmd quot-upper-16
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2))
	   (member (- (* 6 (n)) (p)) '(0 1)))
  :hints (("Goal" :in-theory (enable dp sp hp n p prec f)
                  :use (fnum-vals))))

(local-defthmd quot-upper-17
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(< (sig (a)) (sig (b))))
	   (equal (r (* 3 (n)))
	          (* (expt 4 (1- (* 3 (n))))
		     (mul)
		     (- (sig (a)) (sig (b))))))
  :hints (("Goal" :in-theory (enable n r x d))))

(local-defthmd quot-upper-18
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(< (sig (a)) (sig (b))))
	   (<= (sig (a)) (- (sig (b)) (expt 2 (- 1 (p))))))
  :hints (("Goal" :use (exactp-a exactp-b p-vals) :nonlinearp t)))

(local-defthmd quot-upper-19
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(< (sig (a)) (sig (b))))
	   (<= (r (* 3 (n)))
	       (* (- (expt 2 (- (* 6 (n)) (1+ (p)))))
                  (mul))))
  :hints (("Goal" :use (quot-upper-17 quot-upper-18 p-vals)
                  :nonlinearp t
                  :in-theory (enable n))))

(local-defthmd quot-upper-20
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(< (sig (a)) (sig (b))))
	   (<= (r (* 3 (n)))
	       -9/16))
  :hints (("Goal" :use (quot-upper-19 quot-upper-16 p-vals
                        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3)))
                  :nonlinearp t
                  :in-theory (enable n mul))))

(local-defthmd quot-upper-21
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(>= (sig (a)) (sig (b))))
	   (equal (r (* 3 (n)))
	          (* (expt 4 (1- (* 3 (n))))
		     (mul)
		     (- (/ (sig (a)) 2) (sig (b))))))
  :hints (("Goal" :in-theory (enable n r x d))))

(local-defthmd quot-upper-22
  (implies (and (not (specialp))
                (= (divpow2) 0))
          (>= (sig (b)) 1))
  :hints (("Goal" :use (exactp-b
                        (:instance sig-lower-bound (x (b)))))))

(local-defthmd quot-upper-23
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (<= (* (expt 2 (1- (p))) (sig (a)))
	       (1- (expt 2 (p)))))
  :hints (("Goal" :use (exactp-a p-vals
                        (:instance sig-upper-bound (x (a))))
                  :nonlinearp t)))

(local-defthmd quot-upper-24
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (<= (sig (a)) (- 2 (expt 2 (- 1 (p))))))
  :hints (("Goal" :use (p-vals quot-upper-23)
                  :nonlinearp t)))

(local-defthmd quot-upper-25
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(>= (sig (a)) (sig (b))))
	   (<= (r (* 3 (n)))
	       (- (* (expt 2 (- (* 6 (n)) (+ 2 (p))))
	             (mul)))))
  :hints (("Goal" :in-theory (enable n)
                  :use (p-vals quot-upper-21 quot-upper-22 quot-upper-24)
		  :nonlinearp t)))

(local-defthmd quot-upper-26
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2)
		(>= (sig (a)) (sig (b))))
	   (<= (r (* 3 (n)))
	       -9/32))
  :hints (("Goal" :use (quot-upper-25 fnum-vals
                        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3)))
                  :nonlinearp t
                  :in-theory (enable f p prec sp dp hp n mul))))

(local-defthmd quot-upper-27
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2))
	   (< (r (* 3 (n)))
	      -1/8))
  :hints (("Goal" :use (quot-upper-26 quot-upper-20))))

(local-defthmd quot-upper-28
  (implies (and (not (specialp))
                (= (divpow2) 0)
                (= (quot (* 3 (n))) 2))
           (< (approx (1+ (* 3 (n)))) -3/8))
  :hints (("Goal" :nonlinearp t :use (fnum-vals quot-upper-27 (:instance quot-upper-8 (j (* 3 (n)))))
                  :in-theory (enable n))))

(local-defthmd quot-upper-29
  (implies (and (not (specialp))
		(= (quot (* 3 (n))) 2))
           (<= (q (1+ (* 3 (n)))) -1))
  :hints (("Goal" :use (quot-upper-28 (:instance quot-upper-8 (j (* 3 (n)))))
                  :in-theory (enable quot n m maxk))))

(local-defthmd quot-upper-30
  (implies (and (not (specialp))
		(= (quot (* 3 (n))) 2))
           (< (quot (1+ (* 3 (n)))) 2))
  :hints (("Goal" :use (quot-upper-29)
                  :in-theory (enable quot))))

(local-defthmd quot-upper
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (< (quotf) 2))
  :hints (("Goal" :use (quot-upper-14 quot-upper-15 quot-upper-30)
                  :in-theory (enable quotf))))

(defthmd quot-bounds
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (and (<= 1 (quotf))
	        (< (quotf) 2)))
  :hints (("Goal" :use (quot-upper quot-lower))))

(local-defund remsign ()
  (bitn (bits (+ (+ (rp-3n1) (lognot (rn-3n1))) 1) 58 0) 58))

(local-defund remzero () (log= (logxor (rp-3n1) (rn-3n1)) 0))

(local-defund cin () (lognot1 (remsign)))

(local-defund lsbis2 () (log= (false$) (log= (fnum) 1)))

(local-defund inc () (bits (if1 (lsbis2) 4 2) 2 0))

(local-defund q0 () (bits (+ (qp-3n1) (lognot (qn-3n1))) 53 0))

(local-defund qn1inc ()
  (bits (logxor (logxor (qp-3n1) (bits (lognot (qn-3n1)) 53 0))
                (inc))
        53 0))

(local-defund qp1inc ()
  (bits (ash (logior (logand (qp-3n1) (bits (lognot (qn-3n1)) 53 0))
                     (logand (logior (qp-3n1) (bits (lognot (qn-3n1)) 53 0))
                             (inc)))
             1)
        53 0))

(local-defund q1inc () (bits (+ (+ (qp1inc) (qn1inc)) 1) 53 0))

(local-defund q1low ()
  (bits (+ (+ (bits (qp-3n1) 2 0) (lognot (bits (qn-3n1) 2 0))) 1)
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
  (and (equal (qtrunc)
              (if1 (divpow2)
                   (bits (ash (mana) 1) 52 0)
		   (qtrunc*)))
       (equal (qinc)
              (if1 (divpow2) 0 (qinc*)))
       (equal (stk)
              (if1 (divpow2) 0 (stk*))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(remsign remzero cin lsbis2 inc q0 qn1inc qp1inc q1inc q1low q0inclow q1* q0inc q01
		               q01inc qtrunc* qinc* stk* qtrunc qinc stk computeq))))

(defthm integerp-qinc
  (integerp (qinc))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable computeq-lemma qinc*))))

(local-defund qpf () (qp (1+ (* 3 (n)))))

(local-defund qnf () (qn (1+ (* 3 (n)))))

(local-defund rpf () (rp (1+ (* 3 (n)))))

(local-defund rnf () (rn (1+ (* 3 (n)))))

(local-in-theory (disable (remsign) (remzero) (cin) (lsbis2) (inc) (q0) (qn1inc) (qp1inc) (q1inc) (q1low) (q0inclow) (q1*)
                    (q0inc) (q01) (q01inc) (qtrunc*) (qinc*) (stk*) (qtrunc) (qinc) (stk) (computeq) (qpf) (qnf) (rpf) (rnf)))

(local-defthmd bvecp-qpf-qnf
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (and (bvecp (qpf) (* 6 (n)))
	        (bvecp (qnf) (* 6 (n)))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 3 (n))))))
                  :in-theory (enable n qpf qnf))))

(local-defthmd bvecp-rpf-rnf
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (and (bvecp (rpf) 59)
	        (bvecp (rnf) 59)))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 3 (n))))))
                  :in-theory (enable rpf rnf))))

(local-defthmd q0-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0) (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :in-theory (enable lognot n q0 bits qpf qnf qp-3n1-rewrite qn-3n1-rewrite)
                  :use (bvecp-qpf-qnf))))

(local-defthmd qn1inc-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (qn1inc)
	          (bits (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                (inc))
                        53 0)))
  :hints (("Goal" :in-theory (enable n qn1inc bits-logxor qpf qnf qp-3n1-rewrite qn-3n1-rewrite)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd qn1inc-rewrite-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (qn1inc)
	          (mod (logxor (logxor (qpf) (bits (lognot (qnf)) 53 0))
                                (inc))
                       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits qn1inc-rewrite-1))))

(local-defthmd qp1inc-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (qp1inc)
                  (* 2 (bits (logior (logand (qpf) (bits (lognot (qnf)) 53 0))
                                     (logand (logior (qpf) (bits (lognot (qnf)) 53 0))
                                             (inc)))
			     52 0))))
  :hints (("Goal" :in-theory (enable ash n qp1inc bits-logand bits-logior qpf qnf qp-3n1-rewrite qn-3n1-rewrite)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance bits-shift-up-2 (x (logior (logand (qp-3n1) (bits (lognot (qn-3n1)) 53 0))
                                                              (logand (logior (qp-3n1) (bits (lognot (qn-3n1)) 53 0))
                                                                      (inc))))
			                           (k 1)
						   (i 52))))))

(local-defthmd qp1inc-rewrite-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q1inc)
                  (mod (+ (qpf) (bits (lognot (qnf)) 53 0) (inc) 1)
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable bvecp q1inc-rewrite-3)
                  :use (fnum-vals bvecp-qpf-qnf q1inc-rewrite-4))))

(local-defthmd q1inc-rewrite-6
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q1inc)
                  (mod (+ (qpf) (expt 2 54) (- (qnf)) (inc))
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable n bvecp bits-lognot q1inc-rewrite-5)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1inc-rewrite-7
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q1inc)
                  (mod (+ (qpf) (- (qnf)) (inc))
		       (expt 2 54))))
  :hints (("Goal" :in-theory (enable n bvecp q1inc-rewrite-6)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance mod-mult (m (+ (qpf) (- (qnf)) (inc))) (a 1) (n (expt 2 54)))))))

(local-defthmd q1-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q1low)
                  (mod (- (mod (qpf) 8) (mod (qnf) 8)) 8)))
  :hints (("Goal" :in-theory (enable bits lognot q1low qpf qnf qp-3n1-rewrite qn-3n1-rewrite)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1-rewrite-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q1low)
                  (mod (- (qpf) (qnf)) 8)))
  :hints (("Goal" :in-theory (enable q1-rewrite-1 n bvecp)
                  :use (fnum-vals bvecp-qpf-qnf
		        (:instance mod-sum (a (- (mod (qnf) 8))) (b (qpf)) (n 8))
			(:instance mod-diff (a (qpf)) (b (qnf)) (n 8))))))

(local-defthm integerp-qpf
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (integerp (qpf)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable n) :use (fnum-vals bvecp-qpf-qnf))))

(local-defthm integerp-qnf
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (integerp (qnf)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable n) :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd q1-rewrite-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (bits (q1*) 2 0) (mod (- (qpf) (qnf)) 8)))
  :hints (("Goal" :in-theory (enable q1* q1-rewrite-2 bvecp))))

(local-defthmd q1-rewrite-4
  (implies (and (not (specialp))
                (= (divpow2) 0))
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

(defthmd z-k-l-n
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
                (= (divpow2) 0)
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (fl (/ (- (qpf) (qnf)) 8))
	          (fl (/ (+ (- (qpf) (qnf)) (inc)) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k 1) (l (1+ (inc))) (n 8))))))

(local-defthmd q1-rewrite-6
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (q1inc) 53 3)))
  :hints (("Goal" :in-theory (enable q1-rewrite-2 q1*) :use ((:instance bits-mod-fl (x (q1*)) (i 54) (j 3))))))

(local-defthmd q1-rewrite-7
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (+ (qpf) (- (qnf)) (inc)) 53 3)))
  :hints (("Goal" :in-theory (enable q1inc-rewrite-7)
                  :use (q1-rewrite-6 (:instance mod-bits-equal (x (q1inc)) (y (+ (qpf) (- (qnf)) (inc))) (i 53) (j 3))))))

(local-defthmd q1-rewrite-8
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-5 q1-rewrite-7
                        (:instance bits-mod-fl (x (+ (qpf) (- (qnf)) (inc))) (i 54) (j 3))))))

(local-defthmd q1-rewrite-9
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (fl (/ (- (qpf) (qnf)) 8))
	          (fl (/ (1- (- (qpf) (qnf))) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k 1) (l (1+ (inc))) (n 8))))))

(local-defthmd q1-rewrite-10
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (q0) 53 3)))
  :hints (("Goal" :in-theory (enable q1-rewrite-2 q1*) :use ((:instance bits-mod-fl (x (q1*)) (i 54) (j 3))))))

(local-defthmd q1-rewrite-11
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (mod (1- (- (qpf) (qnf))) (expt 2 54)) (expt 2 54))
	          (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (1- (- (qpf) (qnf)))) (a 54) (b 54))))))

(local-defthmd q1-rewrite-12
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (bits (1- (- (qpf) (qnf))) 53 3)))
  :hints (("Goal" :in-theory (enable q0-rewrite)
                  :use (q1-rewrite-10 q1-rewrite-11 (:instance mod-bits-equal (x (q0)) (y (1- (- (qpf) (qnf)))) (i 53) (j 3))))))

(local-defthmd q1-rewrite-13
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(> (mod (- (qpf) (qnf)) 8) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-9 q1-rewrite-12
                        (:instance bits-mod-fl (x (1- (- (qpf) (qnf)))) (i 54) (j 3))))))

(local-defthmd q1-rewrite-14
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-8 q1-rewrite-13))))

(local-defthmd q1-rewrite-14
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (fl (/ (q1*) 8)) (expt 2 51))
	          (mod (fl (/ (- (qpf) (qnf)) 8)) (expt 2 51))))
  :hints (("Goal" :use (q1-rewrite-8 q1-rewrite-13))))

(local-defthmd q1-rewrite-15
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (* 8 (fl (/ (q1*) 8))) (expt 2 54))
	          (mod (* 8 (fl (/ (- (qpf) (qnf)) 8))) (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-14
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (q1*) 8))))
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (- (qpf) (qnf)) 8))))))))

(local-defthmd q1-rewrite-16
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q1*) (expt 2 54))
	          (mod (+ (mod (* 8 (fl (/ (- (qpf) (qnf)) 8))) (expt 2 54))
		          (mod (- (qpf) (qnf)) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-4 q1-rewrite-15
                        (:instance mod-def (x (q1*)) (y 8))
                        (:instance mod-sum (a (mod (q1*) 8)) (b (* 8 (fl (/ (q1*) 8)))) (n (expt 2 54)))))))


(local-defthmd q1-rewrite-17
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q1*) (expt 2 54))
	          (mod (+ (* 8 (fl (/ (- (qpf) (qnf)) 8)))
		          (mod (- (qpf) (qnf)) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-16
                        (:instance mod-sum (a (mod (- (qpf) (qnf)) 8)) (b (* 8 (fl (/ (- (qpf) (qnf)) 8)))) (n (expt 2 54)))))))

(local-defthmd q1-rewrite-18
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (+ (* 8 (fl (/ (- (qpf) (qnf)) 8)))
		     (mod (- (qpf) (qnf)) 8))
		  (- (qpf) (qnf))))
  :hints (("Goal" :use ((:instance mod-def (x (- (qpf) (qnf))) (y 8))))))

(local-defthmd q1-rewrite-19
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q1*) (expt 2 54))
	          (mod (- (qpf) (qnf)) (expt 2 54))))
  :hints (("Goal" :use (q1-rewrite-17 q1-rewrite-18)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd qp1inc-rewrite-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
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
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (bits (lognot (qnf)) 53 0) (inc))
		       8)))
  :hints (("Goal" :in-theory (enable bvecp q0inc-rewrite-4)
                  :use (q1inc-rewrite-4))))

(local-defthmd q0inc-rewrite-6
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (expt 2 54) (- (bits (qnf) 53 0)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable bits-lognot q0inc-rewrite-5))))

(local-defthmd q0inc-rewrite-7
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (expt 2 54) (- (mod (qnf) (expt 2 54))) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable bits q0inc-rewrite-6))))

(local-defthmd q0inc-rewrite-8
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (mod (qnf) (expt 2 54))) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-7)
                  :use ((:instance mod-mult (m (+ (qpf) (- (mod (qnf) (expt 2 54))))) (a (expt 2 51)) (n 8))))))

(local-defthmd q0inc-rewrite-9
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (mod (mod (qnf) (expt 2 54)) 8)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-8)
                  :use ((:instance mod-diff (a (+ (qpf) (inc) -1)) (b (mod (qnf) (expt 2 54))) (n 8))))))

(local-defthmd q0inc-rewrite-10
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (mod (qnf) 8)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-9)
                  :use ((:instance mod-of-mod-cor (x (qnf)) (a 54) (b 3))))))

(local-defthmd q0inc-rewrite-11
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (q0inclow)
                  (mod (+ (qpf) (- (qnf)) (inc) -1)
		       8)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-10)
                  :use ((:instance mod-diff (a (+ (qpf) (inc) -1)) (b (qnf)) (n 8))))))

(local-defthmd q0inc-rewrite-12
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (bits (q0inc) 2 0)
                  (bits (mod (+ (qpf) (- (qnf)) (inc) -1) 8) 2 0)))
  :hints (("Goal" :in-theory (enable q0inc q0inc-rewrite-11))))

(local-defthmd q0inc-rewrite-13
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q0inc) 8)
                  (mod (+ (qpf) (- (qnf)) (inc) -1) 8)))
  :hints (("Goal" :use (q0inc-rewrite-12) :in-theory (enable bits))))

(local-defthmd q0inc-rewrite-14
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))
	          (fl (/ (+ (- (qpf) (qnf)) (inc)) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k (inc)) (l (1+ (inc))) (n 8))))))

(local-defthmd q0inc-rewrite-15
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (q1inc) 53 3)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-11 q0inc lsbis2 inc) :use ((:instance bits-mod-fl (x (q0inc)) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-16
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (+ (qpf) (- (qnf)) (inc)) 53 3)))
  :hints (("Goal" :in-theory (enable q1inc-rewrite-7)
                  :use (q0inc-rewrite-15 (:instance mod-bits-equal (x (q1inc)) (y (+ (qpf) (- (qnf)) (inc))) (i 53) (j 3))))))

(local-defthmd q0inc-rewrite-17
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (mod (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)) (expt 2 51))))
  :hints (("Goal" :use (q0inc-rewrite-14 q0inc-rewrite-16
                        (:instance bits-mod-fl (x (+ (qpf) (- (qnf)) (inc))) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-18
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))
	          (fl (/ (1- (- (qpf) (qnf))) 8))))
  :hints (("Goal" :in-theory (enable inc)
                  :use ((:instance z-k-l-n (z (1- (- (qpf) (qnf)))) (k (inc)) (l (1+ (inc))) (n 8))))))

(local-defthmd q0inc-rewrite-19
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (q0) 53 3)))
  :hints (("Goal" :in-theory (enable q0inc-rewrite-11 q0inc lsbis2 inc) :use ((:instance bits-mod-fl (x (q0inc)) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-20
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (mod (1- (- (qpf) (qnf))) (expt 2 54)) (expt 2 54))
	          (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (1- (- (qpf) (qnf)))) (a 54) (b 54))))))

(local-defthmd q0inc-rewrite-21
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (bits (1- (- (qpf) (qnf))) 53 3)))
  :hints (("Goal" :in-theory (enable q0-rewrite)
                  :use (q0inc-rewrite-19 q0inc-rewrite-20 (:instance mod-bits-equal (x (q0)) (y (1- (- (qpf) (qnf)))) (i 53) (j 3))))))

(local-defthmd q0inc-rewrite-22
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (mod (+ (- (qpf) (qnf)) (inc) -1) 8) (inc)))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (mod (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)) (expt 2 51))))
  :hints (("Goal" :use (q0inc-rewrite-21 q0inc-rewrite-18
                        (:instance bits-mod-fl (x (1- (- (qpf) (qnf)))) (i 54) (j 3))))))

(local-defthmd q0inc-rewrite-23
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (fl (/ (q0inc) 8)) (expt 2 51))
	          (mod (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)) (expt 2 51))))
  :hints (("Goal" :use (q0inc-rewrite-22 q0inc-rewrite-17))))

(local-defthmd q0inc-rewrite-24
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (* 8 (fl (/ (q0inc) 8))) (expt 2 54))
	          (mod (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))) (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-23
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (q0inc) 8))))
                        (:instance mod-prod (k 8) (n (expt 2 51)) (m (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))))))))

(local-defthmd q0inc-rewrite-25
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q0inc) (expt 2 54))
	          (mod (+ (mod (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))) (expt 2 54))
		          (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-13 q0inc-rewrite-24
                        (:instance mod-def (x (q0inc)) (y 8))
                        (:instance mod-sum (a (mod (q0inc) 8)) (b (* 8 (fl (/ (q0inc) 8)))) (n (expt 2 54)))))))


(local-defthmd q0inc-rewrite-26
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q0inc) (expt 2 54))
	          (mod (+ (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)))
		          (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
		       (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-25
                        (:instance mod-sum (a (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
			                   (b (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8))))
					   (n (expt 2 54)))))))

(local-defthmd q0inc-rewrite-27
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (+ (* 8 (fl (/ (+ (- (qpf) (qnf)) (inc) -1) 8)))
		     (mod (+ (- (qpf) (qnf)) (inc) -1) 8))
		  (+ (- (qpf) (qnf)) (inc) -1)))
  :hints (("Goal" :use ((:instance mod-def (x (+ (- (qpf) (qnf)) (inc) -1)) (y 8))))))

(local-defthmd q0inc-rewrite-28
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q0inc) (expt 2 54))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 54))))
  :hints (("Goal" :use (q0inc-rewrite-26 q0inc-rewrite-27)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd r-rp-rn
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (* (expt 2 56) (rf)) (expt 2 59))
	          (mod (- (rpf) (rnf)) (expt 2 59))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 3 (n))))))
                  :in-theory (enable rf rpf rnf))))

(local-defthmd r-rp-rn
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (* (expt 2 56) (rf)) (expt 2 59))
	          (mod (- (rpf) (rnf)) (expt 2 59))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 3 (n))))))
                  :in-theory (enable rf rpf rnf))))

(local-defthmd rf-bound
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (<= (abs (rf)) (* 2/3 (d))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 3 (n))))))
                  :in-theory (enable rf))))

(local-defthmd r-rp-rn-0
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (iff (= (rf) 0)
	        (= (rpf) (rnf))))
  :hints (("Goal" :use (r-rp-rn bvecp-rpf-rnf rf-bound d-bounds
                        (:instance mod-force-equal (a (* (expt 2 56) (rf))) (b 0) (n (expt 2 59)))
                        (:instance mod-force-equal (a (- (rpf) (rnf))) (b 0) (n (expt 2 59))))
		  :in-theory (enable bvecp))))

(local-defthmd remzero-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remzero)
	          (if (= (logxor (rpf) (rnf)) 0) 1 0)))
  :hints (("Goal" :in-theory (enable remzero rpf rnf))))

(local-defthm integerp-rpf
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (integerp (rpf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthm integerp-rnf
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (integerp (rnf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd remzero-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (remzero)
	          (if (= (rf) 0) 1 0)))
  :hints (("Goal" :use (r-rp-rn-0
                        (:instance logxor-not-0 (x (rpf)) (y (rnf))))
		  :in-theory (enable remzero-rewrite-1))))

(local-defthmd remsign-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsign)
                  (bitn (bits (- (rpf) (rnf)) 58 0) 58)))
  :hints (("Goal" :use (bvecp-rpf-rnf) :in-theory (enable lognot rpf rnf remsign))))

(local-defthmd remsign-rewrite-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsign)
                  (bitn (bits (* (expt 2 56) (rf)) 58 0) 58)))
  :hints (("Goal" :use (r-rp-rn) :in-theory (enable remsign-rewrite-1 bits))))

(local-defthmd remsign-rewrite-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsign)
                  (if (< (si (bits (* (expt 2 56) (rf)) 58 0) 59) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable si remsign-rewrite-2)
                  :use ((:instance bits-bounds (x (* (expt 2 56) (rf))) (i 58) (j 0))))))

(local-defthmd int-rf
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (integerp (* (expt 2 56) (rf))))
  :hints (("Goal" :in-theory (enable rf)
                  :use ((:instance int-r (j (1+ (* 3 (n)))))))))

(local-defthmd remsign-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsign)
                  (if (< (rf) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable remsign-rewrite-3)
                  :nonlinearp t
                  :use (rf-bound d-bounds int-rf (:instance si-bits (x (* (expt 2 56) (rf))) (n 59))))))

(local-defthmd quot-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (<= (abs (- (* (expt 2 (* 6 (n))) (/ (x) (d)))
	               (* (expt 2 (* 6 (n))) (quotf))))
	       2/3))
  :hints (("Goal" :use (q-error) :nonlinearp t)))

(local-defthmd quot-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (iff (>= (* (expt 2 (* 6 (n))) (/ (x) (d)))
	            (* (expt 2 (* 6 (n))) (quotf)))
		(>= (rf) 0)))
  :hints (("Goal" :use (d-bounds) :in-theory (enable rf quotf r) :nonlinearp t)))

(local-defthmd quot-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (integerp (* (expt 2 (* 6 (n))) (quotf))))
  :hints (("Goal" :use ((:instance int-quot (j (1+ (* 3 (n))))))
                  :in-theory (enable quotf))))

(local-defthmd quot-4
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
	   (equal (fl (* (expt 2 (* 6 (n))) (/ (x) (d))))
	          (* (expt 2 (* 6 (n))) (quotf))))
  :hints (("Goal" :use (quot-1 quot-2 quot-3
                        (:instance fl-unique (x (* (expt 2 (* 6 (n))) (/ (x) (d)))) (n (* (expt 2 (* 6 (n))) (quotf))))))))

(local-defthmd quot-5
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
	   (equal (cin) 1))
  :hints (("Goal" :in-theory (enable cin remsign-rewrite))))

(local-defthmd quot-6
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (mod (q01) (expt 2 54))
	          (mod (- (qpf) (qnf)) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q01 quot-5)
                  :use (q1-rewrite-19))))

(local-defthmd quot-7
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (mod (q01) (expt 2 (* 6 (n))))
	          (mod (- (qpf) (qnf)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-6
                        (:instance mod-of-mod-cor (x (q01)) (a 54) (b (* 6 (n))))
                        (:instance mod-of-mod-cor (x (- (qpf) (qnf))) (a 54) (b (* 6 (n))))))))

(local-defthmd quot-8
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (* (expt 2 (* 6 (n))) (- (quotf) (q 1)))
	          (- (qpf) (qnf))))
  :hints (("Goal" :in-theory (enable qpf qnf quotf)
                  :use ((:instance induction-result (j (1+ (* 3 (n)))))))))

(local-defthmd quot-9
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (* (expt 2 (* 6 (n))) (- (quotf) (q 1))) (expt 2 (* 6 (n))))
	          (mod (- (qpf) (qnf)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-8) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-10
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (* (expt 2 (* 6 (n))) (quotf)) (expt 2 (* 6 (n))))
	          (mod (- (qpf) (qnf)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-9 (:instance mod-mult (m (* (expt 2 (* 6 (n))) (quotf))) (a (- (q 1))) (n (expt 2 (* 6 (n)))))))))

(local-defthmd quot-11
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (mod (q01) (expt 2 (* 6 (n))))
	          (mod (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-4 quot-7 quot-10))))

(local-defthmd quot-12
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (mod (q01inc) (expt 2 54))
	          (mod (+ (- (qpf) (qnf)) (inc)) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q01inc quot-5)
                  :use (q1inc-rewrite-7))))

(local-defthmd quot-13
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (mod (q01inc) (expt 2 (* 6 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-12
                        (:instance mod-of-mod-cor (x (q01inc)) (a 54) (b (* 6 (n))))
                        (:instance mod-of-mod-cor (x (+ (- (qpf) (qnf)) (inc))) (a 54) (b (* 6 (n))))))))

(local-defthmd quot-14
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (+ (inc) (* (expt 2 (* 6 (n))) (- (quotf) (q 1))))
	          (+ (- (qpf) (qnf)) (inc))))
  :hints (("Goal" :use (quot-8))))

(local-defthmd quot-15
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (+ (inc) (* (expt 2 (* 6 (n))) (- (quotf) (q 1)))) (expt 2 (* 6 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-14) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-16
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (+ (* (expt 2 (* 6 (n))) (quotf)) (inc)) (expt 2 (* 6 (n))))
	          (mod (+ (inc) (* (expt 2 (* 6 (n))) (- (quotf) (q 1)))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use ((:instance mod-mult (m (+ (* (expt 2 (* 6 (n))) (quotf)) (inc))) (a (- (q 1))) (n (expt 2 (* 6 (n)))))))))

(local-defthmd quot-17
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (mod (q01inc) (expt 2 (* 6 (n))))
	          (mod (+ (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (inc)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-4 quot-13 quot-15 quot-16))))

(local-defthmd quot-18
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
	   (equal (fl (* (expt 2 (* 6 (n))) (/ (x) (d))))
	          (1- (* (expt 2 (* 6 (n))) (quotf))))	          )
  :hints (("Goal" :use (quot-1 quot-2 quot-3
                        (:instance fl-unique (x (* (expt 2 (* 6 (n))) (/ (x) (d)))) (n (1- (* (expt 2 (* 6 (n))) (quotf)))))))))

(local-defthmd quot-19
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
	   (equal (cin) 0))
  :hints (("Goal" :in-theory (enable cin remsign-rewrite))))

(in-theory (disable ACL2::|(mod (- x) y)|))

(local-defthmd quot-20
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (mod (q01) (expt 2 54))
	          (mod (1- (- (qpf) (qnf))) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q0-rewrite q01 quot-19)
                  :use ((:instance mod-of-mod-cor (x (q0)) (a 54) (b 54))))))

(local-defthmd quot-21
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (mod (q01) (expt 2 (* 6 (n))))
	          (mod (1- (- (qpf) (qnf))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-20
                        (:instance mod-of-mod-cor (x (q01)) (a 54) (b (* 6 (n))))
                        (:instance mod-of-mod-cor (x (1- (- (qpf) (qnf)))) (a 54) (b (* 6 (n))))))))

(local-defthmd quot-22
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (1- (* (expt 2 (* 6 (n))) (- (quotf) (q 1))))
	          (1- (- (qpf) (qnf)))))
  :hints (("Goal" :use (quot-8))))

(local-defthmd quot-23
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (1- (* (expt 2 (* 6 (n))) (- (quotf) (q 1)))) (expt 2 (* 6 (n))))
	          (mod (1- (- (qpf) (qnf))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-22) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-24
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (1- (* (expt 2 (* 6 (n))) (- (quotf) (q 1)))) (expt 2 (* 6 (n))))
	          (mod (1- (* (expt 2 (* 6 (n))) (quotf))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use ((:instance mod-mult (m (1- (* (expt 2 (* 6 (n))) (quotf)))) (a (- (q 1))) (n (expt 2 (* 6 (n)))))))))

(local-defthmd quot-25
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (mod (q01) (expt 2 (* 6 (n))))
	          (mod (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-18 quot-21 quot-23 quot-24))))

(local-defthmd quot-26
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (mod (q01inc) (expt 2 54))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 54))))
  :hints (("Goal" :in-theory (enable bits q01inc quot-19)
                  :use (q0inc-rewrite-28 (:instance mod-of-mod-cor (x (q0inc)) (a 54) (b 54))))))

(local-defthmd quot-27
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (mod (q01inc) (expt 2 (* 6 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 (* 6 (n))))))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quot-26
                        (:instance mod-of-mod-cor (x (q01inc)) (a 54) (b (* 6 (n))))
                        (:instance mod-of-mod-cor (x (+ (- (qpf) (qnf)) (inc) -1)) (a 54) (b (* 6 (n))))))))

(local-defthmd quot-28
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (+ (* (expt 2 (* 6 (n))) (- (quotf) (q 1))) (inc) -1)
	          (+ (- (qpf) (qnf)) (inc) -1)))
  :hints (("Goal" :use (quot-8))))

(local-defthmd quot-29
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (+ (* (expt 2 (* 6 (n))) (- (quotf) (q 1))) (inc) -1) (expt 2 (* 6 (n))))
	          (mod (+ (- (qpf) (qnf)) (inc) -1) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-28) :in-theory (theory 'minimal-theory))))

(local-defthmd quot-30
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (+ (* (expt 2 (* 6 (n))) (- (quotf) (q 1))) (inc) -1) (expt 2 (* 6 (n))))
	          (mod (+ (* (expt 2 (* 6 (n))) (quotf)) (inc) -1) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use ((:instance mod-mult (m (+ (* (expt 2 (* 6 (n))) (quotf)) (inc) -1)) (a (- (q 1))) (n (expt 2 (* 6 (n)))))))))

(local-defthmd quot-31
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (mod (q01inc) (expt 2 (* 6 (n))))
	          (mod (+ (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (inc)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-18 quot-27 quot-29 quot-30))))

(local-defthmd quot-32
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q01) (expt 2 (* 6 (n))))
	          (mod (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-11 quot-25))))

(local-defthmd quot-33
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (q01inc) (expt 2 (* 6 (n))))
	          (mod (+ (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (inc)) (expt 2 (* 6 (n))))))
  :hints (("Goal" :use (quot-17 quot-31))))

(local (in-theory (disable ash-rewrite)))

(defthmd qtrunc-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p)))))
  :hints (("Goal" :use (quot-32 fnum-vals
                        (:instance mod-of-mod-cor (x (q01)) (a 53) (b (p)))
                        (:instance mod-of-mod-cor (x (fl (/ (q01) 2))) (a 53) (b (p)))
                        (:instance fl-mod (a (q01)) (n 2) (m (expt 2 (p))))
                        (:instance fl-mod (a (fl (* (expt 2 (* 6 (n))) (/ (x) (d))))) (n 2) (m (expt 2 (p)))))
                  :in-theory (enable ash-rewrite bits prec dp sp hp p f n computeq-lemma qtrunc* lsbis2))))

(local-defthm qinc-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (FL (+ 2 (* 1/2 (FL (* 18014398509481984 (/ (D)) (X))))))
                  (+ 2 (FL (* 9007199254740992 (/ (D)) (X))))))
  :hints (("Goal" :use ((:instance fl+int-rewrite (x (/ (fl (* (expt 2 54) (/ (x) (d)))) 2)) (n 2))
                        (:instance fl/int-rewrite (x (* (expt 2 54) (/ (x) (d)))) (n 2))))))

(local-defthm qinc-rewrite-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (FL (+ 2 (* 1/2 (FL (* 4096 (/ (D)) (X))))))
                  (+ 2 (FL (* 2048 (/ (D)) (X))))))
  :hints (("Goal" :use ((:instance fl+int-rewrite (x (/ (fl (* (expt 2 12) (/ (x) (d)))) 2)) (n 2))
                        (:instance fl/int-rewrite (x (* (expt 2 12) (/ (x) (d)))) (n 2))))))

(defthmd qinc-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (p)) (/ (x) (d)))) 2) (expt 2 (p)))))
  :hints (("Goal" :use (quot-33 fnum-vals d-bounds
                        (:instance mod-of-mod-cor (x (q01inc)) (a 53) (b (p)))
                        (:instance mod-of-mod-cor (x (fl (/ (q01inc) 2))) (a 53) (b (p)))
                        (:instance fl-mod (a (q01inc)) (n 2) (m (expt 2 (p))))
                        (:instance fl-mod (a (+ (fl (* (expt 2 (* 6 (n))) (/ (x) (d)))) (inc))) (n 2) (m (expt 2 (p)))))
                  :in-theory (enable ash-rewrite bits prec dp sp hp p f n computeq-lemma qinc* inc lsbis2))))

(local-defthmd stk-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (stk)
	          (if (= (* (expt 2 (* 6 (n))) (/ (x) (d)))
		         (* (expt 2 (* 6 (n))) (quotf)))
		      0 1)))
  :hints (("Goal" :nonlinearp t :use (d-bounds) :in-theory (enable rf quotf r remzero-rewrite stk* computeq-lemma))))

(local-defthmd stk-2
  (implies (and (integerp n) (rationalp x) (< (abs (- x n)) 1))
           (iff (integerp x) (= x n))))

(local-defthmd stk-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (stk)
	          (if (integerp (* (expt 2 (* 6 (n))) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :in-theory (enable stk-1)
                  :use (d-bounds quot-1 quot-3
		        (:instance stk-2 (x (* (expt 2 (* 6 (n))) (/ (x) (d)))) (n (* (expt 2 (* 6 (n))) (quotf))))))))

(local-defthmd stk-4
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(not (member (fnum) '(0 2))))
	   (= (* 6 (n)) (p)))
  :hints (("Goal" :in-theory (enable prec p f dp sp hp n)
                  :use (fnum-vals))))

(local-defthmd stk-5
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(member (fnum) '(0 2)))
	   (= (* 6 (n)) (1+ (p))))
  :hints (("Goal" :in-theory (enable prec p f dp sp hp n)
                  :use (fnum-vals))))

(local-defthmd stk-6
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(member (fnum) '(0 2))
		(integerp (* (expt 2 (p)) (/ (x) (d)))))
	   (integerp (* (expt 2 (* 6 (n))) (/ (x) (d)))))
  :hints (("Goal" :in-theory (enable prec p f dp sp hp n)
                  :use (fnum-vals))))

(local-defund s () (* (expt 2 (1+ (p))) (/ (x) (d))))

(local-defthmd stk-7
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(member (fnum) '(0 2))
		(not (integerp (* (expt 2 (p)) (/ (x) (d)))))
	        (integerp (* (expt 2 (* 6 (n))) (/ (x) (d)))))
	   (and (integerp (s)) (oddp (s))))
  :hints (("Goal" :in-theory (enable s) :use (stk-5))))

(local-defthmd stk-8
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (* (expt 2 (1+ (p))) (x))
	          (* (s) (d))))
  :hints (("Goal" :in-theory (enable s))))

(local-in-theory (disable (s)))

(local-defthm stk-9
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(integerp (s))
		(oddp (s)))
	   (or (equal (* (expt 2 (1+ (p))) (sig (a)))
	              (* (s) (sig (b))))
	       (equal (* (expt 2 (+ 2 (p))) (sig (a)))
	              (* (s) (sig (b))))))
  :rule-classes ()
  :hints (("Goal" :use (stk-8 p-vals (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))) :in-theory (enable x d mul))))

(local-defthm stk-10
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(integerp (s))
		(oddp (s)))
	   (and (integerp (* (s) (sig (b))))
	        (evenp (* (s) (sig (b))))))
  :rule-classes ()
  :hints (("Goal" :use (p-vals stk-9 exactp-a))))

(local-defun leastk (n)
  (declare (xargs :measure (nfix (- (p) n))
                  :hints (("Goal" :use (p-vals)))))
  (if (and (natp n) (< n (1- (p))))
      (if (integerp (* (expt 2 n) (sig (b))))
          n
	(leastk (1+ n)))
    (1- (p))))

(local-in-theory (disable (leastk)))

(local-defthmd leastk-int
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(natp n)
		(< n (1- (p)))
		(not (integerp (* (expt 2 n) (sig (b))))))
           (let ((k (leastk n)))
	     (and (natp k)
	          (integerp (* (expt 2 k) (sig (b))))
		  (oddp (* (expt 2 k) (sig (b)))))))
  :hints (("Subgoal *1/" :use (p-vals exactp-b))))

(local-defund lk () (leastk 0))

(local-in-theory (disable (lk)))

(local-defthmd lk-int
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (and (natp (lk))
	        (integerp (* (expt 2 (lk)) (sig (b))))
		(oddp (* (expt 2 (lk)) (sig (b))))))
  :hints (("Goal" :in-theory (enable lk)
                  :use (p-vals
                        (:instance sig-upper-bound (x (b)))
                        (:instance sig-lower-bound (x (b)))
                        (:instance leastk-int (n 0))))))

(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))

(local-defthmd stk-11
  (implies (and (integerp a)
                (oddp a)
		(integerp b)
                (oddp b))
	   (oddp (* a b)))
  :hints (("Goal" :in-theory (enable divides) :use ((:instance euclid (p 2))))))

(local-defthm stk-12
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(local-defthm stk-13
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(integerp (lk))
                (<= 0 (lk))
		(integerp (* 1/2 (s) (sig (b)))))
	   (integerp (* (s) (sig (b)) (expt 2 (+ -1 (lk))))))
  :hints (("goal" :use ((:instance stk-12 (x (* 1/2 (S) (SIG (B)))) (y (expt 2 (lk))))))))

(local-defthmd stk-14
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(member (fnum) '(0 2))
	        (integerp (* (expt 2 (* 6 (n))) (/ (x) (d)))))
           (integerp (* (expt 2 (p)) (/ (x) (d)))))
  :hints (("Goal" :use (stk-7 stk-10 lk-int stk-13
                        (:instance stk-11 (a (s)) (b (* (expt 2 (lk)) (sig (b)))))))))

(defthmd stk-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (stk-3 stk-4 stk-6 stk-14))))

(local-defthmd qtrunc-divpow2-1
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (equal (sig (a))
	          (1+ (/ (mana) (expt 2 (1- (p)))))))
  :hints (("Goal" :in-theory (enable divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (a-class fnum-vals spec-fields (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-2
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (equal (sig (b)) 1))
  :hints (("Goal" :in-theory (enable divpow2 encodingp normp denormp decode b f dp sp hp prec p)
                  :use (b-class fnum-vals spec-fields (:instance sig-ndecode (x (opbw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-3
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (>= (sig (a)) 1))
  :hints (("Goal" :in-theory (enable divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (a-class fnum-vals spec-fields (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-4
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (equal (sig (a))
	          (/ (x) (d))))
  :hints (("Goal" :in-theory (enable x d mul qtrunc-divpow2-1 qtrunc-divpow2-2)
                  :use (qtrunc-divpow2-3 (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(defthmd qtrunc-divpow2-5
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (and (integerp (qtrunc))
	        (equal (qtrunc) (* 2 (mana)))))
  :hints (("Goal" :in-theory (enable bvecp ash qtrunc divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (bvecp-mana a-class fnum-vals spec-fields (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-6
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (and (integerp (qtrunc))
	        (integerp (* (expt 2 (p)) (/ (x) (d))))
	        (equal (* (expt 2 (p)) (/ (x) (d)))
	               (+ (expt 2 (p)) (qtrunc)))))
  :hints (("Goal" :use (p-vals bvecp-mana qtrunc-divpow2-4) :in-theory (enable qtrunc-divpow2-5 qtrunc-divpow2-1))))

(local-defthmd qtrunc-divpow2-7
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (+ (expt 2 (p)) (qtrunc)) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-divpow2-6 p-vals (:instance mod-mult (m (qtrunc)) (a 1) (n (expt 2 (p))))))))

(local-defthmd qtrunc-divpow2-8
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (fl (* (expt 2 (p)) (/ (x) (d))))
	          (* (expt 2 (p)) (/ (x) (d)))))
  :hints (("Goal" :use (qtrunc-divpow2-6 p-vals))))

(defthmd qtrunc-rewrite-divpow2
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-divpow2-6 qtrunc-divpow2-7 qtrunc-divpow2-8))))

(defthmd qtrunc-rewrite-gen
  (implies (not (specialp))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-rewrite qtrunc-rewrite-divpow2))))

(defthmd stk-rewrite-divpow2
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (and (integerp (* (expt 2 (p)) (/ (x) (d))))
	        (equal (stk) 0)))
  :hints (("Goal" :use (qtrunc-divpow2-6) :in-theory (enable stk))))

(defthmd stk-rewrite-gen
  (implies (not (specialp))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (stk-rewrite stk-rewrite-divpow2))))
