(in-package "RTL")

(include-book "normalize")

(defund x ()
  (if (specialp)
      1/4
      (if (evenp (si (expshft) 13))
          (/ (sig (a)) 2)
        (/ (sig (a)) 4))))

(in-theory (disable (x)))

(defthm x-bounds
  (and (>= (x) 1/4)
       (< (x) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable x)
                  :use (a-pos
		        (:instance sig-lower-bound (x (a)))
		        (:instance sig-upper-bound (x (a)))))))

(defthm integerp-expq
  (implies (not (specialp))
           (integerp (expq)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable expq-rewrite))))

(local-defthmd sqrt-a-x-1
  (implies (and (not (specialp))
                (oddp (si (expshft) 13)))
           (equal (a)
	          (* (expt 2 (* 2 (1+ (- (expq) (bias (f))))))
		     (x))))
  :hints (("Goal" :in-theory (enable x siga-rewrite expq-rewrite dp sp hp p prec bias f)
                  :use (a-siga fnum-vals))))

(local-defthmd sqrt-a-x-2
  (implies (and (not (specialp))
                (evenp (si (expshft) 13)))
           (equal (a)
	          (* (expt 2 (* 2 (1+ (- (expq) (bias (f))))))
		     (x))))
  :hints (("Goal" :in-theory (enable x siga-rewrite expq-rewrite dp sp hp p prec bias f)
                  :use (a-siga fnum-vals))))

(defthmd a-x
  (implies (not (specialp))
           (equal (a)
	          (* (expt 2 (* 2 (1+ (- (expq) (bias (f))))))
		     (x))))
  :hints (("Goal" :in-theory (enable sqrt-a-x-1 sqrt-a-x-2 dp sp hp p prec bias f)
                  :cases ((evenp (si (expshft) 13)))
                  :use (fnum-vals))))

(defund quot (j)
  (if (zp j)
      1
    (+ (quot (1- j))
       (* (expt 4 (- j)) (q j)))))

(defund r (j)
  (* (expt 4 j)
     (- (x) (* (quot j) (quot j)))))

(in-theory (disable (quot) (r)))

(defthmd q-1-vals
  (member (q-1) '(-2 -1 0))
  :hints (("Goal" :in-theory (enable firstiter q-1))))

(defthmd q-vals
  (member (q j) '(-2 -1 0 1 2))
  :hints (("Goal" :expand ((q j)) :in-theory (enable nextdigit firstiter q-1))))

(defthm integerp-q
  (integerp (q j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (q-vals))))

(defthm rat-quot
  (rationalp (quot j))
  :hints (("Goal" :in-theory (enable quot)))
  :rule-classes (:type-prescription :rewrite))

(defthmd int-quot
  (implies (natp j)
           (integerp (* (expt 4 j) (quot j))))
  :hints (("Goal" :use ((:functional-instance
                         int-quot-sqrt
                         (e% (lambda () 2))
			 (r% (lambda () 4))
                         (a% (lambda () 2))
			 (rho% (lambda () 2/3))
			 (q% q)
			 (quot% quot)
			 (rem% r)
			 (x% x))))
          ("Subgoal 5" :in-theory (enable r quot))
          ("Subgoal 4" :use (q-vals))
          ("Subgoal 3" :use (q-vals x-bounds))
          ("Subgoal 2" :use (x-bounds))
          ("Subgoal 1" :use (x-bounds))))

(local-defthmd quot-exact-1
  (<= (abs (1- (quot j))) (* 2/3 (- 1 (expt 4 (- (nfix j))))))
  :hints (("Goal" :in-theory (enable quot) :induct (quot j))
          ("Subgoal *1/2" :nonlinearp t :use (q-vals))))

(defthmd quot-exact-2
  (<= (abs (1- (quot j))) 2/3)
  :hints (("Goal" :use (quot-exact-1))))

(defthmd quot-exact-3
  (member (expo (quot j)) '(0 -1 -2))
  :hints (("Goal" :use (quot-exact-2
                        (:instance expo<= (x (quot j)) (n 0))
                        (:instance expo>= (x (quot j)) (n -2))))))

(local-defthmd quot-exact-4
  (implies (and (natp j) (<= j (n)))
           (exactp (quot j) (+ (* 2 j) 1 (expo (quot j)))))
  :hints (("Goal" :use (quot-exact-3 int-quot fnum-vals) :in-theory (enable n exactp2))))

(defthmd quot-exact
  (implies (and (natp j) (<= j (n)))
           (exactp (quot j) (1+ (* 2 (n)))))
  :hints (("Goal" :use (quot-exact-3 quot-exact-4 fnum-vals) :in-theory (enable exactp-<= n))))

(defthmd r0-rewrite
  (equal (r 0) (1- (x)))
  :hints (("Goal" :use ((:functional-instance
                         rem0-sqrt-rewrite
                         (e% (lambda () 2))
			 (r% (lambda () 4))
                         (a% (lambda () 2))
			 (rho% (lambda () 2/3))
			 (q% q)
			 (quot% quot)
			 (rem% r)
			 (x% x))))
          ("Subgoal 2" :in-theory (enable r quot) :use (x-bounds))
          ("Subgoal 1" :in-theory (enable r quot) :use (x-bounds))))

(defthmd r-recurrence
  (implies (natp j)
           (equal (r (+ 1 j))
                  (- (* 4 (r j))
                     (* (q (1+ j))
		        (+ (* 2 (quot j))
			   (* (expt 4 (- (1+ j)))
			      (q (1+ j))))))))
  :hints (("Goal" :use ((:functional-instance
                         rem-sqrt-recurrence
                         (e% (lambda () 2))
			 (r% (lambda () 4))
                         (a% (lambda () 2))
			 (rho% (lambda () 2/3))
			 (q% q)
			 (quot% quot)
			 (rem% r)
			 (x% x))))))

(defund blo (j)
  (- (* 4/9 (expt 4 (- j)))
     (* 2 2/3 (quot j))))

(defund bhi (j)
  (+ (* 4/9 (expt 4 (- j)))
     (* 2 2/3 (quot j))))

(defthmd r0-bounds
  (and (<= (blo 0) (r 0))
       (>= (bhi 0) (r 0)))
  :hints (("Goal" :use ((:functional-instance
                         rem0-sqrt-bounds
                         (blo% blo)
                         (bhi% bhi)
                         (e% (lambda () 2))
			 (r% (lambda () 4))
                         (a% (lambda () 2))
			 (rho% (lambda () 2/3))
			 (q% q)
			 (quot% quot)
			 (rem% r)
			 (x% x))))
          ("Subgoal 2" :in-theory (enable r quot) :use (blo bhi))
          ("Subgoal 1" :in-theory (enable r quot) :use (blo bhi))))

(defthm r-bounds
  (implies (natp j)
           (iff (and (<= (expt (- (quot j) (* 2/3 (expt 4 (- j)))) 2)
                         (x))
                     (>= (expt (+ (quot j) (* 2/3 (expt 4 (- j)))) 2)
                         (x)))
                (and (<= (blo j) (r j))
		     (>= (bhi j) (r j)))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance
                         blohi
                         (blo% blo)
                         (bhi% bhi)
                         (e% (lambda () 2))
			 (r% (lambda () 4))
                         (a% (lambda () 2))
			 (rho% (lambda () 2/3))
			 (q% q)
			 (quot% quot)
			 (rem% r)
			 (x% x))))
          ("Subgoal 2" :in-theory (enable r quot) :use (blo bhi))
          ("Subgoal 1" :in-theory (enable r quot) :use (blo bhi))))

(defund rp4 (j) (bits (ash (rp j) 2) 58 0))
         
(defund rn4 (j) (bits (ash (rn j) 2) 58 0))

(defund rs8 (j)
  (bits (+ (+ (bits (rp4 j) 58 51)
              (lognot (bits (rn4 j) 58 51)))
           (logior1 (bitn (rp4 j) 50)
                    (lognot1 (bitn (rn4 j) 50))))
        7 0))

(defund rs7 (j) (bits (rs8 j) 7 1))

(defund approx (j)
  (if (zp j)
      (* 4 (r 0))
    (* 1/8 (si (rs7 j) 7))))

 (in-theory (disable (approx)))

(defthm ratp-approx
  (rationalp (approx j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable r si rs7 approx))))

(defund approx-bounds (j k)
  (and (implies (< (approx j) (ms4 (i j) j k))
                (< (* 4 (r j)) (ms4 (i j) j k)))
       (implies (>= (approx j) (ms4 (i j) j k))
                (> (* 4 (r j)) (- (ms4 (i j) j k) 1/32)))))

(defund approx-inv (j)
  (and (= (q (1+ j)) (select-digit-s4 (approx j) (i j) j))
       (approx-bounds j 2)
       (approx-bounds j 1)
       (approx-bounds j 0)
       (approx-bounds j -1)))

(defund r-bnds-inv (j)
  (and (<= (blo j) (r j))
       (>= (bhi j) (r j))))

(defund quot-bnds-inv (j)
  (and (<= 1/2 (quot j))
       (>= 1 (quot j))))

(defund srt-inv (j)
  (and (quot-bnds-inv j)
       (r-bnds-inv j)
       (approx-inv j)))

(defund srt-hyp (j)
  (if (zp j)
      (srt-inv 0)
    (and (srt-inv j)
         (srt-hyp (1- j)))))

(local-defthm i-rewrite-1
  (member (i 1) '(0 4 8))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable firstiter i i-1))))

(local-defthm i-rewrite-2
  (equal (i 1) (* 16 (- (quot 1) 1/2)))
  :hints (("Goal" :in-theory (enable quot q q-1 firstiter i i-1))))

(local-defthm i-rewrite-3
  (equal (i 2) (* 16 (- (quot 2) 1/2)))
  :hints (("Goal" :use (i-rewrite-1)
                  :in-theory (enable quot q i i-rewrite-2 i))))

(local-defthm i-rewrite-4
  (implies (zp j)
           (equal (i j) (* 16 (- (quot j) 1/2))))
  :hints (("Goal" :in-theory (enable quot i))))

(local-defthm i-rewrite-5
  (implies (and (natp j) (>= j 3))
           (equal (i j) (i (1- j))))
  :hints (("Goal" :in-theory (enable i))))

(local-defthmd i-rewrite
  (equal (i j)
         (* 16 (- (quot (min (nfix j) 2)) 1/2)))
  :hints (("Goal" :in-theory (enable quot) :induct (quot j))
          ("Subgoal *1/2" :expand ((quot 2) (quot 1)) :cases ((zp j) (= j 0) (= j 1) (= j 2)))))

(local-in-theory (disable i-rewrite-2 i-rewrite-3 i-rewrite-4 i-rewrite-5))

(defthmd srt-step
  (implies (and (natp j)
		(srt-hyp j))
	   (and (quot-bnds-inv (1+ j))
                (r-bnds-inv (1+ j))))
  :hints (("Goal" :use ((:functional-instance
                         srt-sqrt-rad-4
                         (blo% blo)
                         (bhi% bhi)
                         (e% (lambda () 2))
			 (r% (lambda () 4))
                         (a% (lambda () 2))
			 (rho% (lambda () 2/3))
			 (q% q)
			 (quot% quot)
			 (rem% r)
			 (x% x)
                         (approx% approx)
                         (approx%-bounds approx-bounds)
                         (approx%-inv approx-inv)
                         (i% i)
                         (quot%-bnds-inv quot-bnds-inv)
                         (rem%-bnds-inv r-bnds-inv)
                         (s4-inv srt-inv)
                         (s4-hyp srt-hyp))))
          ("Subgoal 7" :in-theory (enable r-bnds-inv))
          ("Subgoal 6" :in-theory (enable quot-bnds-inv))
          ("Subgoal 5" :in-theory (enable srt-hyp))
          ("Subgoal 4" :in-theory (enable srt-inv))
          ("Subgoal 3" :in-theory (enable approx-inv))
          ("Subgoal 2" :in-theory (enable approx-bounds))
          ("Subgoal 1" :in-theory (enable i-rewrite))))
