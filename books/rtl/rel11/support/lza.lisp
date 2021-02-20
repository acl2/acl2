(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "basic")
(include-book "bits")
(include-book "log")
(include-book "float")
(include-book "ppa")

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)|
                                |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
				simplify-products-gather-exponents-equal mod-cancel-*-const
				cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)|
				|(equal x (if a b c))| |(equal (if a b c) x)| mod-theorem-one-b))

(local-defun assumps (a b n)
  (and (not (zp n))
       (bvecp a n)
       (bvecp b n)
       (> (+ a b) (expt 2 n))))

(defund p0 (a b)
  (declare (xargs :guard (and (integerp a)
                              (integerp b))))
  (logxor a b))

(defund g0 (a b)
  (declare (xargs :guard (and (integerp a)
                              (integerp b))))
  (logand a b))

(defund k0 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (logand (bits (lognot a) (1- n) 0) (bits (lognot b) (1- n) 0)))

(defund w0 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (bits (lognot (logxor (p0 a b) (* 2 (k0 a b n)))) (1- n) 0))

(local-defthmd bvecp-w0
  (implies (assumps a b n)
           (bvecp (w0 a b n) n))
  :hints (("Goal" :in-theory (enable w0))))

(defthmd p0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(integerp j))
	   (equal (bitn (p0 a b) j)
	          (if (= (bitn a j) (bitn b j))
		      0 1)))
  :hints (("Goal" :in-theory (enable p0 bitn-logxor)
                  :use ((:instance bitn-0-1 (x a) (n j))
		        (:instance bitn-0-1 (x b) (n j))))))

(defthmd g0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(integerp j))
	   (equal (bitn (g0 a b) j)
	          (if (and (= (bitn a j) 1) (= (bitn b j) 1))
		      1 0)))
  :hints (("Goal" :in-theory (enable g0 bitn-logand)
                  :use ((:instance bitn-0-1 (x a) (n j))
		        (:instance bitn-0-1 (x b) (n j))))))

(defthmd k0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(natp j)
                (natp n)
                (< j n))
	   (equal (bitn (k0 a b n) j)
	          (if (and (= (bitn a j) 0) (= (bitn b j) 0))
		      1 0)))
  :hints (("Goal" :in-theory (enable k0 bitn-bits bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x a))
			(:instance bitn-0-1 (n j) (x b))
			(:instance bitn-0-1 (n j) (x (lognot a)))
			(:instance bitn-0-1 (n j) (x (lognot b)))
			(:instance bitn-lognot (n j) (x a))
			(:instance bitn-lognot (n j) (x b))))))

(defthmd w0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
                (not (zp j))
		(< j n))
	   (equal (bitn (w0 a b n) j)
	          (if (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j)))
		      1 0)))
  :hints (("Goal" :in-theory (enable w0 bitn-bits bitn-logxor bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x (p0 a b)))
			(:instance bitn-0-1 (n (1- j)) (x (k0 a b n)))
			(:instance bitn-0-1 (n j) (x (lognot (logxor (p0 a b) (* 2 (k0 a b n))))))
			(:instance bitn-lognot (x (logxor (p0 a b) (* 2 (k0 a b n)))) (n j))
			(:instance bitn-shift-up (x (k0 a b n)) (k 1) (n (1- j)))))))

(local-defund conds (a b n j)
  (and (= (bits (w0 a b n) (1- n) (1+ j)) 0)
       (= (bits (+ a b) (1- n) (1+ j)) 0)
       (or (>= (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))
           (= (bitn (k0 a b n) j) 1))))

(local-defund goal (a b n)
  (and (>= (w0 a b n) 2)
       (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w0 a b n)))
           (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w0 a b n)))))))

(local-defthm conds-127
  (implies (assumps a b n) (conds a b n (1- n)))
  :hints (("Goal" :in-theory (enable assumps conds))))

(local-defthmd s-127-0
  (implies (assumps a b n)
           (not (equal (bits (+ a b) (1- n) 0) 0)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use ((:instance bitn-plus-bits (x (+ a b)) (m 0))
		        (:instance bitn-0-1 (x (+ a b)))))))

(local-defthmd conds-0-1
  (implies (and (assumps a b n) (conds a b n 0))
           (equal (bitn (+ a b) 0) 1))
  :hints (("Goal" :in-theory (enable assumps conds)
                 :use (s-127-0
		       (:instance bitn-0-1 (x (+ a b)) (n 0))
                       (:instance bits-plus-bitn (x (+ a b)) (n (1- n)) (m 0))))))

(local-defthmd conds-0-2
  (implies (and (assumps a b n) (conds a b n 0))
           (equal (bitn (+ a b) 0)
	          (mod (+ (bitn a 0) (bitn b 0)) 2)))
  :hints (("Goal" :in-theory (enable bitn-rec-0)
                  :use ((:instance mod-sum (n 2) (a a) (b b))
		        (:instance mod-sum (n 2) (b a) (a (mod b 2)))))))

(local-defthm conds-0
  (implies (assumps a b n) (not (conds a b n 0)))
  :hints (("Goal" :in-theory (enable conds)
                  :use (conds-0-1 conds-0-2
		        (:instance k0-rewrite (j 0))
                        (:instance bitn-0-1 (n 0) (x a))
			(:instance bitn-0-1 (n 0) (x b))))))

(local-defthmd w0-1-1
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 1))
           (equal (expo (w0 a b n)) j))
  :hints (("Goal" :in-theory (enable conds bvecp)
                  :nonlinearp t
                  :use (bvecp-w0
                        (:instance expo>= (x (w0 a b n)) (n j))
			(:instance expo<= (x (w0 a b n)) (n j))
			(:instance bitn-plus-bits (x (w0 a b n)) (n j) (m 0))
			(:instance bits-plus-bits (x (w0 a b n)) (n (1- n)) (p (1+ j)) (m 0))
			(:instance bits-bounds (x (w0 a b n)) (i (1- j)) (j 0))))))

(local-defthmd w0-1-2
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 1))
           (equal (bitn (p0 a b) j) (bitn (k0 a b n) (1- j))))
  :hints (("Goal" :in-theory (enable w0-rewrite))))

(local-defthmd w0-1-3
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 1))
           (not (= (bitn (p0 a b) j) 1)))
  :hints (("Goal" :use (w0-1-2
                        (:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j))
                        (:instance bitn-0-1 (x a) (n (1- j)))
                        (:instance bitn-0-1 (x b) (n (1- j)))
			(:instance bitn-plus-bits (x a) (n j) (m 0))
			(:instance bitn-plus-bits (x b) (n j) (m 0))
			(:instance bitn-plus-bits (x a) (n (1- j)) (m 0))
			(:instance bitn-plus-bits (x b) (n (1- j)) (m 0))
			(:instance bits-bounds (x a) (i (- j 2)) (j 0))
			(:instance bits-bounds (x b) (i (- j 2)) (j 0)))
                  :in-theory (enable conds p0-rewrite k0-rewrite)
		  :nonlinearp t)))

(local-defthmd w0-1-4
  (implies (and (natp a) (natp b) (natp j))
           (equal (bits (+ a b) j 0)
                  (mod (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use ((:instance mod-sum (n (expt 2 (1+ j))) (a a) (b b))
		        (:instance mod-sum (n (expt 2 (1+ j))) (b a) (a (mod b (expt 2 (1+ j)))))))))

(local-defthmd w0-1-5
  (implies (and (natp a) (natp b) (not (zp j)) (= (bitn (p0 a b) j) 0))
           (equal (bits (+ a b) j 0)
	          (+ (bits a (1- j) 0) (bits b (1- j) 0))))
  :hints (("Goal" :use ((:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j))
			(:instance bitn-plus-bits (x a) (n j) (m 0))
			(:instance bitn-plus-bits (x b) (n j) (m 0))
         		(:instance bits-bounds (x a) (i (1- j)) (j 0))
			(:instance bits-bounds (x b) (i (1- j)) (j 0)))
		  :nonlinearp t
                  :in-theory (enable w0-1-4 p0-rewrite))))

(local-defthmd w0-1-6
  (implies (and (assumps a b n)
                (not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 1)
		(= (bitn (p0 a b) j) 0))
           (equal (bits (+ a b) (1- n) 0)
	          (+ (bits a (1- j) 0) (bits b (1- j) 0))))
  :hints (("Goal" :use ((:instance bits-plus-bits (x (+ a b)) (n (1- n)) (p (1+ j)) (m 0)))
                  :in-theory (enable w0-1-5 conds))))

(local-defthmd w0-1-7
  (implies (and (assumps a b n)
                (not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 1)
		(= (bitn (p0 a b) j) 0))
           (and (>= (expo (bits (+ a b) (1- n) 0)) (1- j))
	        (<= (expo (bits (+ a b) (1- n) 0)) j)))
  :hints (("Goal" :use (w0-1-6 (:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j))
			(:instance bitn-0-1 (x a) (n (1- j)))
                        (:instance bitn-0-1 (x b) (n (1- j)))
			(:instance bitn-plus-bits (x a) (n (1- j)) (m 0))
			(:instance bitn-plus-bits (x b) (n (1- j)) (m 0))
			(:instance bits-bounds (x a) (i (- j 2)) (j 0))
			(:instance bits-bounds (x b) (i (- j 2)) (j 0))
			(:instance expo>= (x (bits (+ a b) (1- n) 0)) (n (1- j)))
			(:instance expo<= (x (bits (+ a b) (1- n) 0)) (n j)))
		  :nonlinearp t
                  :in-theory (enable w0-rewrite p0-rewrite k0-rewrite))))

(local-defthmd w0-1
  (implies (and (assumps a b n)
                (not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 1))
           (goal a b n))
  :hints (("Goal" :use (w0-1-3 w0-1-7
                        (:instance bvecp-bitn-0 (x (w0 a b n)) (n j))
                        (:instance bitn-0-1 (x (p0 a b)) (n j)))
		  :nonlinearp t
                  :in-theory (e/d (bvecp goal w0-1-1) (bvecp-bitn-0)))))

(local-defthmd w0-0-1
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (equal (bits (w0 a b n) (1- n) j) 0))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w0 a b n)) (n (1- n)) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w0-0-2
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
	       (expt 2 j)))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w0 a b n)) (n (1- n)) (m j))
                        (:instance bitn-plus-bits (x a) (n j) (m 0))
                        (:instance bitn-plus-bits (x b) (n j) (m 0))
			(:instance bitn-0-1 (x a) (n j))
			(:instance bitn-0-1 (x b) (n j)))
		  :nonlinearp t
                  :in-theory (enable conds p0-rewrite k0-rewrite))))

(local-defthm w0-0-3
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (or (= (bitn (k0 a b n) (1- j)) 1)
	       (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-2)
                  :in-theory (enable conds p0-rewrite k0-rewrite w0-rewrite))))

(local-defthm w0-0-4
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (or (= (bitn (k0 a b n) (1- j)) 1)
	       (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-2)
                  :in-theory (enable conds p0-rewrite k0-rewrite w0-rewrite))))

(local-in-theory (disable ACL2::|(mod (+ x y) z) where (<= 0 z)|))

(local-defthmd w0-0-5
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (equal (bits (+ a b) j 0)
	          (mod (+ (expt 2 j) (bits a (1- j) 0) (bits b (1- j) 0))
		       (expt 2 (1+ j)))))
  :hints (("Goal" :use (w0-0-2
                        (:instance bitn-plus-bits (x a) (n j) (m 0))
                        (:instance bitn-plus-bits (x b) (n j) (m 0))
                        (:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j)))
                  :in-theory (enable w0-1-4 p0-rewrite))))

(local-defthmd w0-0-6
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (equal (bits (+ a b) j 0)
                  (mod (- (+ (bits a (1- j) 0) (bits b (1- j) 0)) (expt 2 j)) (expt 2 (1+ j)))))
  :hints (("Goal" :use (w0-0-5
                        (:instance mod-mult (m (- (+ (bits a (1- j) 0) (bits b (1- j) 0)) (expt 2 j)))
			                    (n (expt 2 (1+ j)))
					    (a 1)))
		  ;:nonlinearp t
                  :in-theory (enable w0-rewrite p0-rewrite k0-rewrite))))

(local-defthm w0-0-7
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-2 w0-0-6
			(:instance bits-bounds (x a) (i (1- j)) (j 0))
			(:instance bits-bounds (x b) (i (1- j)) (j 0)))
		  :nonlinearp t)))

(local-defthm w0-0-8
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0)
		(= (bitn (p0 a b) j) 0)
		(= (bitn (k0 a b n) j) 1))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j))
			(:instance bitn-0-1 (x a) (n (1- j)))
                        (:instance bitn-0-1 (x b) (n (1- j)))
                        (:instance bitn-plus-bits (x a) (n j) (m 0))
                        (:instance bitn-plus-bits (x b) (n j) (m 0))
                        (:instance bitn-plus-bits (x a) (n (1- j)) (m 0))
                        (:instance bitn-plus-bits (x b) (n (1- j)) (m 0))
			(:instance bits-bounds (x a) (i (- j 2)) (j 0))
			(:instance bits-bounds (x b) (i (- j 2)) (j 0)))
		  :nonlinearp t
                  :in-theory (enable w0-1-4 w0-rewrite p0-rewrite k0-rewrite))))

(local-defthm w0-0-9
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0)
		(= (bitn (p0 a b) j) 0)
		(= (bitn (k0 a b n) j) 0))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j))
			(:instance bitn-0-1 (x a) (n (1- j)))
                        (:instance bitn-0-1 (x b) (n (1- j)))
                        (:instance bitn-plus-bits (x a) (n j) (m 0))
                        (:instance bitn-plus-bits (x b) (n j) (m 0))
                        (:instance bitn-plus-bits (x a) (n (1- j)) (m 0))
                        (:instance bitn-plus-bits (x b) (n (1- j)) (m 0))
			(:instance bits-bounds (x a) (i (- j 2)) (j 0))
			(:instance bits-bounds (x b) (i (- j 2)) (j 0)))
		  :nonlinearp t
                  :in-theory (enable w0-1-4 w0-rewrite p0-rewrite k0-rewrite))))

(local-defthm w0-0-10
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-7 w0-0-8 w0-0-9)
                  :in-theory (enable p0-rewrite k0-rewrite))))

(local-defthm w0-0-11
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (equal (bitn (+ a b) j) 0))
  :hints (("Goal" :use (w0-0-10
                        (:instance bitn-0-1 (x (+ a b)) (n j))
                        (:instance bitn-plus-bits (x (+ a b)) (n j) (m 0))))))

(local-defthm w0-0-12
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (equal (bits (+ a b) (1- n) j) 0))
  :hints (("Goal" :use (w0-0-11 (:instance bits-plus-bitn (x (+ a b)) (n (1- n)) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w0-0
  (implies (and (assumps a b n)
                (not (zp j))
		(< j n)
		(conds a b n j)
		(= (bitn (w0 a b n) j) 0))
           (conds a b n (1- j)))
  :hints (("Goal" :use (w0-0-1 w0-0-4 w0-0-12)
                  :in-theory (enable conds))))

(local-defthm conds-goal
  (implies (and (natp j) (< j n) (conds a b n j) (assumps a b n))
           (goal a b n))
  :rule-classes ()
  :hints (("Goal" :induct (nats j))
          ("Subgoal *1/2" :use (w0-1 w0-0 (:instance bitn-0-1 (x (w0 a b n)) (n j))))))

(local-defthm assumps-goal
  (implies (assumps a b n) (goal a b n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance conds-goal (j (1- n)))))))

(defthm lza-thm
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (and (>= (w0 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w0 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w0 a b n)))))))
  :rule-classes ()
  :hints (("Goal" :use assumps-goal :in-theory (enable goal))))

;;--------------------------------------------------------------------------------

(local-defun assumps+ (a b n)
  (and (assumps a b n)
       (not (= (expo (bits (+ a b 1) (1- n) 0))
               (expo (bits (+ a b) (1- n) 0))))))

(local-defthmd lza-cor-1
  (implies (assumps+ a b n)
	   (equal (bits (+ 1 a b) (+ -1 n) 0)
	          (1+ (bits (+ a b) (+ -1 n) 0))))
  :hints (("Goal" :in-theory (enable bvecp bits-mod)
                  :nonlinearp t
                  :use ((:instance mod-force (m (+ a b)) (a 1) (n (expt 2 n)))
		        (:instance mod-force (m (+ 1 a b)) (a 1) (n (expt 2 n)))))))

(local-defun e (a b n)
  (expo (bits (+ 1 a b) (1- n) 0)))

(local-defthmd lza-cor-2
  (implies (assumps+ a b n)
	   (and (not (zp (e a b n)))
	        (< (e a b n) n)))
  :hints (("Goal" :use (lza-cor-1
			(:instance expo-monotone (x 2) (y (bits (+ 1 a b) (+ -1 n) 0)))
			(:instance expo<= (x (bits (+ 1 a b) (+ -1 n) 0)) (n (1- n)))
			(:instance bits-bounds (x (+ 1 a b)) (i (1- n)) (j 0))))))


(local-defthmd lza-cor-3
  (implies (assumps+ a b n)
	   (< (bits (+ a b) (+ -1 n) 0)
	      (expt 2 (e a b n))))
  :hints (("Goal" :use (lza-cor-1
			(:instance expo>= (x (bits (+ a b) (+ -1 n) 0))
			                  (n (e a b n)))
			(:instance expo-monotone (x (bits (+ a b) (+ -1 n) 0))
			                         (y (bits (+ 1 a b) (+ -1 n) 0)))))))

(local-defthmd lza-cor-4
  (implies (assumps+ a b n)
	   (equal (bits (+ a b) (+ -1 n) 0)
	          (1- (expt 2 (e a b n)))))
  :hints (("Goal" :use (lza-cor-1 lza-cor-2 lza-cor-3
                        (:instance expo-lower-bound (x (bits (+ 1 a b) (+ -1 n) 0)))))))

(local-defthmd lza-cor-5
  (implies (assumps+ a b n)
	   (equal (bitn (1- (expt 2 (e a b n))) 0)
	          1))
  :hints (("Goal" :in-theory (enable bitn-rec-0)
                  :use (lza-cor-2
                        (:instance mod-plus-mod-2 (b -1)
			                          (a (expt 2 (e a b n))))
			(:instance mod012 (m (1- (expt 2 (e a b n)))))))))

(local-defthmd lza-cor-6
  (implies (assumps+ a b n)
	   (equal (bitn (+ a b) 0)
	          1))
  :hints (("Goal" :use (lza-cor-4 lza-cor-5
                        (:instance bitn-bits (x (+ a b)) (i (1- n)) (j 0) (k 0))))))

(local-defthmd lza-cor-7
  (implies (assumps+ a b n)
	   (or (and (= (bitn a 0) 0)
	            (= (bitn b 0) 1))
	       (and (= (bitn a 0) 1)
	            (= (bitn b 0) 0))))
  :hints (("Goal" :in-theory (enable bitn-rec-0)
                  :use (lza-cor-6 mod-plus-mod-2
		        (:instance mod012 (m (+ a b)))
			(:instance mod012 (m a))
			(:instance mod012 (m b))))))

(local-defthmd lza-cor-8-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (assumps (1+ a) b n))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (lza-cor-1
                        (:instance logior-2**n (x a) (n 0))
			(:instance logior-bvecp (x a) (y 1))))))

(local-defthmd lza-cor-9-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (or (= (expo (bits (+ 1 a b) (1- n) 0)) (expo (w0 (1+ a) b n)))
               (= (expo (bits (+ 1 a b) (1- n) 0)) (1- (expo (w0 (1+ a) b n))))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (lza-cor-8-a
		        (:instance lza-thm (a (1+ a)))))))

(local-defthmd lza-cor-10-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (1+ a) (1- n) 1)
	          (bits a (1- n) 1)))
  :hints (("Goal" :use (lza-cor-8-a
                        (:instance bits-plus-bitn (x a) (n (1- n)) (m 0))
			(:instance bits-plus-bitn (x (1+ a)) (n (1- n)) (m 0))))))

(local-defthmd lza-cor-11-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (lognot (1+ a)) (1- n) 1)
	          (bits (lognot a) (1- n) 1)))
  :hints (("Goal" :use (lza-cor-10-a
                        (:instance bits-lognot (x a) (i (1- n)) (j 1))
                        (:instance bits-lognot (x (1+ a)) (i (1- n)) (j 1))))))

(local-defthmd lza-cor-12-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (p0 (1+ a) b) (1- n) 1)
	          (bits (p0 a b) (1- n) 1)))
  :hints (("Goal" :use (lza-cor-10-a)
                  :in-theory (enable p0 bits-logxor))))

(local-defthmd lza-cor-13-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (k0 (1+ a) b n) (1- n) 1)
	          (bits (k0 a b n) (1- n) 1)))
  :hints (("Goal" :use (lza-cor-11-a)
                  :in-theory (enable k0 bits-logand))))

(local-defthmd lza-cor-14-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bitn (k0 (1+ a) b n) 0)
	          (bitn (k0 a b n) 0)))
  :hints (("Goal" :use (lza-cor-7)
                  :in-theory (enable k0-rewrite))))

(local-defthmd lza-cor-15-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (k0 (1+ a) b n) (1- n) 0)
	          (bits (k0 a b n) (1- n) 0)))
  :hints (("Goal" :use (lza-cor-13-a lza-cor-14-a
                        (:instance bits-plus-bitn (x (k0 (1+ a) b n)) (n (1- n)) (m 0))
			(:instance bits-plus-bitn (x (k0 a b n)) (n (1- n)) (m 0))))))

(local-defthmd lza-cor-16-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (* 2 (k0 (1+ a) b n)) n 1)
	          (bits (* 2 (k0 a b n)) n 1)))
  :hints (("Goal" :use (lza-cor-15-a
                        (:instance bits-shift-up-1 (x (k0 (1+ a) b n)) (k 1) (i n) (j 1))
			(:instance bits-shift-up-1 (x (k0 a b n)) (k 1) (i n) (j 1))))))

(local-defthmd lza-cor-17-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (* 2 (k0 (1+ a) b n)) (1- n) 1)
	          (bits (* 2 (k0 a b n)) (1- n) 1)))
  :hints (("Goal" :in-theory (disable bits-bits)
                  :use (lza-cor-16-a
                        (:instance bits-bits (x (* 2 (k0 (1+ a) b n))) (i n) (j 1) (k (- n 2)) (l 0))
                        (:instance bits-bits (x (* 2 (k0 a b n))) (i n) (j 1) (k (- n 2)) (l 0))))))

(local-defthmd lza-cor-18-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (bits (w0 (1+ a) b n) (1- n) 1)
	          (bits (w0 a b n) (1- n) 1)))
  :hints (("Goal" :in-theory (enable w0 bits-logxor)
                  :use (lza-cor-12-a lza-cor-17-a
                        (:instance bits-lognot (x (logxor (p0 a b) (* 2 (k0 a b n))))
			           (i (1- n)) (j 1))
                        (:instance bits-lognot (x (logxor (p0 (1+ a) b) (* 2 (k0 (1+ a) b n))))
			           (i (1- n)) (j 1))))))

(local-defthmd lza-cor-19-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (fl (/ (w0 (1+ a) b n) 2))
	          (fl (/ (w0 a b n) 2))))
  :hints (("Goal" :in-theory (enable w0 bits)
                  :use (lza-cor-18-a
                        (:instance bits-mod (x (w0 a b n)) (i (1- n)))
                        (:instance bits-mod (x (w0 (1+ a) b n)) (i (1- n)))))))

;; Move this to lib/float.lisp:

(local-defthmd expo-fl
  (implies (and (rationalp x)
                (>= x 1))
	   (equal (expo (fl x)) (expo x)))
  :hints (("Goal" :use (expo-lower-bound
                        (:instance expo-monotone (x (fl x)) (y x))
                        (:instance expo>= (n 0))
                        (:instance expo>= (x (fl x)) (n (expo x)))))))

(local-defthmd lza-cor-20-a
  (implies (and (assumps+ a b n)
                (= (bitn a 0) 0))
           (equal (expo (w0 (1+ a) b n))
	          (expo (w0 a b n))))
  :hints (("Goal" ;:in-theory (enable expo-fl)
                  :use (lza-cor-8-a lza-cor-19-a lza-thm
		        (:instance lza-thm (a (1+ a)))
		        (:instance expo-fl (x (/ (w0 (1+ a) b n) 2)))
		        (:instance expo-fl (x (/ (w0 a b n) 2)))
                        (:instance expo-shift (x (w0 (1+ a) b n)) (n -1))
                        (:instance expo-shift (x (w0 a b n)) (n -1))))))

(local-defthmd lza-cor-8-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (assumps a (1+ b) n))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (lza-cor-1
                        (:instance logior-2**n (x b) (n 0))
			(:instance logior-bvecp (x b) (y 1))))))

(local-defthmd lza-cor-9-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (or (= (expo (bits (+ 1 a b) (1- n) 0)) (expo (w0 a (1+ b) n)))
               (= (expo (bits (+ 1 a b) (1- n) 0)) (1- (expo (w0 a (1+ b) n))))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (lza-cor-8-b
		        (:instance lza-thm (b (1+ b)))))))

(local-defthmd lza-cor-10-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (1+ b) (1- n) 1)
	          (bits b (1- n) 1)))
  :hints (("Goal" :use (lza-cor-8-b
                        (:instance bits-plus-bitn (x b) (n (1- n)) (m 0))
			(:instance bits-plus-bitn (x (1+ b)) (n (1- n)) (m 0))))))

(local-defthmd lza-cor-11-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (lognot (1+ b)) (1- n) 1)
	          (bits (lognot b) (1- n) 1)))
  :hints (("Goal" :use (lza-cor-10-b
                        (:instance bits-lognot (x b) (i (1- n)) (j 1))
                        (:instance bits-lognot (x (1+ b)) (i (1- n)) (j 1))))))

(local-defthmd lza-cor-12-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (p0 a (1+ b)) (1- n) 1)
	          (bits (p0 a b) (1- n) 1)))
  :hints (("Goal" :use (lza-cor-10-b)
                  :in-theory (enable p0 bits-logxor))))

(local-defthmd lza-cor-13-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (k0 a (1+ b) n) (1- n) 1)
	          (bits (k0 a b n) (1- n) 1)))
  :hints (("Goal" :use (lza-cor-11-b)
                  :in-theory (enable k0 bits-logand))))

(local-defthmd lza-cor-14-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bitn (k0 a (1+ b) n) 0)
	          (bitn (k0 a b n) 0)))
  :hints (("Goal" :use (lza-cor-7)
                  :in-theory (enable k0-rewrite))))

(local-defthmd lza-cor-15-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (k0 a (1+ b) n) (1- n) 0)
	          (bits (k0 a b n) (1- n) 0)))
  :hints (("Goal" :use (lza-cor-13-b lza-cor-14-b
                        (:instance bits-plus-bitn (x (k0 a (1+ b) n)) (n (1- n)) (m 0))
			(:instance bits-plus-bitn (x (k0 a b n)) (n (1- n)) (m 0))))))

(local-defthmd lza-cor-16-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (* 2 (k0 a (1+ b) n)) n 1)
	          (bits (* 2 (k0 a b n)) n 1)))
  :hints (("Goal" :use (lza-cor-15-b
                        (:instance bits-shift-up-1 (x (k0 a (1+ b) n)) (k 1) (i n) (j 1))
			(:instance bits-shift-up-1 (x (k0 a b n)) (k 1) (i n) (j 1))))))

(local-defthmd lza-cor-17-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (* 2 (k0 a (1+ b) n)) (1- n) 1)
	          (bits (* 2 (k0 a b n)) (1- n) 1)))
  :hints (("Goal" :in-theory (disable bits-bits)
                  :use (lza-cor-16-b
                        (:instance bits-bits (x (* 2 (k0 a (1+ b) n))) (i n) (j 1) (k (- n 2)) (l 0))
                        (:instance bits-bits (x (* 2 (k0 a b n))) (i n) (j 1) (k (- n 2)) (l 0))))))

(local-defthmd lza-cor-18-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (bits (w0 a (1+ b) n) (1- n) 1)
	          (bits (w0 a b n) (1- n) 1)))
  :hints (("Goal" :in-theory (enable w0 bits-logxor)
                  :use (lza-cor-12-b lza-cor-17-b
                        (:instance bits-lognot (x (logxor (p0 a b) (* 2 (k0 a b n))))
			           (i (1- n)) (j 1))
                        (:instance bits-lognot (x (logxor (p0 a (1+ b)) (* 2 (k0 a (1+ b) n))))
			           (i (1- n)) (j 1))))))

(local-defthmd lza-cor-19-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (fl (/ (w0 a (1+ b) n) 2))
	          (fl (/ (w0 a b n) 2))))
  :hints (("Goal" :in-theory (enable w0 bits)
                  :use (lza-cor-18-b
                        (:instance bits-mod (x (w0 a b n)) (i (1- n)))
                        (:instance bits-mod (x (w0 a (1+ b) n)) (i (1- n)))))))

(local-defthmd lza-cor-20-b
  (implies (and (assumps+ a b n)
                (= (bitn b 0) 0))
           (equal (expo (w0 a (1+ b) n))
	          (expo (w0 a b n))))
  :hints (("Goal" ;:in-theory (enable expo-fl)
                  :use (lza-cor-8-b lza-cor-19-b lza-thm
		        (:instance lza-thm (b (1+ b)))
		        (:instance expo-fl (x (/ (w0 a (1+ b) n) 2)))
		        (:instance expo-fl (x (/ (w0 a b n) 2)))
                        (:instance expo-shift (x (w0 a (1+ b) n)) (n -1))
                        (:instance expo-shift (x (w0 a b n)) (n -1))))))

(defthm lza-cor
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w0 a b n)))
               (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w0 a b n))))))
  :rule-classes ()
  :hints (("Goal" :use (lza-thm lza-cor-7 lza-cor-8-a lza-cor-8-b lza-cor-20-a lza-cor-20-b
                        (:instance lza-thm (a (1+ a)))
		        (:instance lza-thm (b (1+ b)))))))

;;----------------------------------------------------------------------------------------

(local-defthmd lza-cor-21
  (implies (assumps+ a b n)
           (and (equal (bits (+ a b) (e a b n) 0) (1- (expt 2 (e a b n))))
	        (equal (bits (+ a b) (1- (e a b n)) 0) (1- (expt 2 (e a b n))))))
  :hints (("Goal" :in-theory (e/d (bvecp) (bits-bits))
                  :use (lza-cor-2 lza-cor-4
                        (:instance bits-bits (x (+ a b)) (i (1- n)) (j 0) (k (e a b n)) (l 0))
			(:instance bits-bits (x (+ a b)) (i (1- n)) (j 0) (k (1- (e a b n))) (l 0))))))

(local-defthmd lza-cor-22
  (implies (assumps+ a b n)
           (and (not (equal (bits (logxor a b) (e a b n) 0) (1- (expt 2 (1+ (e a b n))))))
	        (equal (bits (logxor a b) (1- (e a b n)) 0) (1- (expt 2 (e a b n))))))
  :hints (("Goal" :use (lza-cor-21
                        (:instance lutz-lemma (x a) (y b) (n (e a b n)))
			(:instance lutz-lemma (x a) (y b) (n (1+ (e a b n))))))))

(local-defthmd lza-cor-23
  (implies (assumps+ a b n)
           (equal (bitn (p0 a b) (e a b n)) 0))
  :hints (("Goal"  :in-theory (enable p0)
                   :use (lza-cor-22
                        (:instance bitn-plus-bits (x (logxor a b)) (n (e a b n)) (m 0))))))

(local-defthmd lza-cor-24
  (implies (assumps+ a b n)
	   (equal (bitn (logxor a b) (1- (e a b n))) 1))
  :hints (("Goal"  :nonlinearp t
                   :cases ((= (e a b n) 1) (> (e a b n) 1))
		   :use (lza-cor-22 lza-cor-2
                        (:instance bitn-plus-bits (x (logxor a b)) (n (1- (e a b n))) (m 0))
                        (:instance bitn-0-1 (x (logxor a b)) (n (1- (e a b n))))
			(:instance bits-bounds (x (logxor a b)) (i (- (e a b n) 2)) (j 0))))))

(local-defthmd lza-cor-25
  (implies (assumps+ a b n)
	   (equal (bitn (k0 a b n) (1- (e a b n))) 0))
  :hints (("Goal"  :in-theory (enable bitn-logxor k0-rewrite)
		   :use (lza-cor-24 lza-cor-2
                         (:instance bitn-0-1 (x a) (n (1- (e a b n))))
                         (:instance bitn-0-1 (x b) (n (1- (e a b n))))))))

(local-defthmd lza-cor-26
  (implies (assumps+ a b n)
	   (equal (bitn (w0 a b n) (e a b n)) 1))
  :hints (("Goal"  :in-theory (enable w0-rewrite)
                   :use (lza-cor-23 lza-cor-25 lza-cor-2))))

(local-defthmd lza-cor-27
  (implies (assumps+ a b n)
	   (>= (expo (w0 a b n)) (e a b n)))
  :hints (("Goal"  :in-theory (enable bvecp)
                   :use (lza-cor-26
		         (:instance expo>= (x (w0 a b n)) (n (e a b n)))))))

(local-defthmd lza-cor-28
  (implies (assumps+ a b n)
	   (equal (expo (bits (+ a b) (1- n) 0))
	          (1- (e a b n))))
  :hints (("Goal"  :nonlinearp t
                   :use (lza-cor-2 lza-cor-4
                         (:instance expo-unique (x (bits (+ a b) (1- n) 0)) (n (1- (e a b n))))))))

(local-defthm lza-cor-alt
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w0 a b n)))
               (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w0 a b n))))))
  :rule-classes ()
  :hints (("Goal" :use (lza-thm lza-cor-27 lza-cor-28))))

(defthm lza-thm-1-case-2
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (and (>= (w0 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w0 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w0 a b n)))))
                (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w0 a b n)))
                    (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w0 a b n)))))))
  :rule-classes ()
  :hints (("Goal" :use (lza-thm lza-cor-alt))))

;;----------------------------------------------------------------------------------------

(local-defthmd lza-special-10
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
 	   (equal (bitn (w0 a b n) 0)
	          (if (= (bitn (p0 a b) 0) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable bitn-bits bitn-logxor w0 p0-rewrite)
	          :use ((:instance bitn-shift-up (x (k0 a b n)) (k 1) (n -1))
		        (:instance bitn-lognot (x (LOGXOR (P0 A B) (* 2 (K0 A B N)))) (n 0))))))

(local-defthmd lza-special-11
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n)))
 	   (equal (bitn a 0) (bitn b 0)))
  :hints (("Goal" :use (mod-plus-mod-2 (:instance mod012 (m a)) (:instance mod012 (m b)))
	          :in-theory (e/d (bitn-rec-0 bits-mod) (ACL2::|(mod x 2)|)))))

(local-defthmd lza-special-12
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n)))
 	   (equal (bitn (w0 a b n) 0)
	          1))
  :hints (("Goal" :use (lza-special-11)
	          :in-theory (enable lza-special-10 p0-rewrite))))

(defund inset (a b n i)
  (or (and (= (bitn (p0 a b) i) 1) (= (bitn (p0 a b) (1- i)) 1))
      (and (= (bitn (p0 a b) i) 1) (= (bitn (g0 a b) (1- i)) 1))
      (and (= (bitn (g0 a b) i) 1) (= (bitn (k0 a b n) (1- i)) 1))
      (and (= (bitn (k0 a b n) i) 1) (= (bitn (k0 a b n) (1- i)) 1))))

(local-defthmd lza-special-13
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(not (zp i))
		(< i n)
		(inset a b n i))
	   (equal (bitn (w0 a b n) i)
	          0))
  :hints (("Goal" :in-theory (enable inset w0-rewrite p0-rewrite k0-rewrite g0-rewrite))))

(local-defthmd lza-special-14
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(natp j))
           (iff (= (bitn (p0 a b) (1+ j)) (bitn (+ a b) (1+ j)))
	        (< (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable p0 bitn-logxor gen-val)
                  :use ((:instance bitn-0-1 (x a) (n (1+ j)))
		        (:instance bitn-0-1 (x b) (n (1+ j)))
		        (:instance ripple-carry-lemma (x a) (y b) (i (1+ j)) (cin 0))
		        (:instance cbit-rewrite (x a) (y b) (i j) (cin 0))))))

(local-defthmd lza-special-15
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(natp i)
		(< i n))
	   (equal (bitn (+ a b) i)
	          0))		  
  :hints (("Goal" :in-theory (enable bitn-expt-0))))

(local-defthmd lza-special-16
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (p0 a b) i) 1))
	   (>= (+ (bits a (1- i) 0) (bits b (1- i) 0))
	       (expt 2 i)))
  :hints (("Goal" :use (lza-special-15 (:instance lza-special-14 (j (1- i)))))))

(local-defthmd lza-special-17
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (p0 a b) i) 1))
	   (equal (bitn (k0 a b n) (1- i)) 0))
  :hints (("Goal" :in-theory (enable k0-rewrite)
                  :nonlinearp t
                  :use (lza-special-16
                        (:instance bitn-plus-bits (x a) (n (1- i)) (m 0))
                        (:instance bitn-plus-bits (x b) (n (1- i)) (m 0))
                        (:instance bitn-0-1 (x a) (n (1- i)))
			(:instance bits-bounds (x a) (i (- i 2)) (j 0))
                        (:instance bitn-0-1 (x b) (n (1- i)))
			(:instance bits-bounds (x b) (i (- i 2)) (j 0))))))

(local-defthmd lza-special-20
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (p0 a b) i) 1))
	   (inset a b n i))
  :hints (("Goal" :use (lza-special-17)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite inset))))

(local-defthmd lza-special-21
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n))
	   (equal (mod (+ (bits a i 0) (bits b i 0)) (expt 2 (1+ i)))
	          (bits (+ a b) i 0)))
  :hints (("Goal" :use ((:instance mod-sum (a (bits a i 0)) (n (expt 2 (1+ i))))
                        (:instance mod-sum (a b) (b a) (n (expt 2 (1+ i)))))
		  :nonlinearp t
		  :in-theory (enable bits-mod))))

(local-defthmd lza-special-22
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (k0 a b n) i) 1))
	   (equal (+ (bits a i 0) (bits b i 0))
	          (bits (+ a b) i 0)))
  :hints (("Goal" :use (lza-special-21
                        (:instance bitn-plus-bits (x a) (n i) (m 0))
                        (:instance bitn-plus-bits (x b) (n i) (m 0))
			(:instance bits-bounds (x a) (i (1- i)) (j 0))
			(:instance bits-bounds (x b) (i (1- i)) (j 0)))
		  :nonlinearp t
		  :in-theory (enable k0-rewrite))))

(local-defthmd lza-special-23
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (k0 a b n) i) 1))
	   (equal (+ (bits a i 0) (bits b i 0))
	          0))
  :hints (("Goal" :use (lza-special-22 (:instance bits-plus-mult-2 (x 0) (y 1) (k n) (n i) (m 0))))))

(local-defthmd lza-special-24
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (k0 a b n) i) 1))
	   (equal (bitn (k0 a b n) (1- i))
	          1))
  :hints (("Goal" :use (lza-special-23
                        (:instance bitn-bits (x a) (j 0) (k (1- i)))
                        (:instance bitn-bits (x b) (j 0) (k (1- i))))
		  :in-theory (enable k0-rewrite))))

(local-defthmd lza-special-26
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (k0 a b n) i) 1))
	   (inset a b n i))
  :hints (("Goal" :use (lza-special-24)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite inset))))

(local-defthmd lza-special-27
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n))
	   (equal (mod (+ (bits a (1- i) 0) (bits b (1- i) 0)) (expt 2 i))
	          (bits (+ a b) (1- i) 0)))
  :hints (("Goal" :use ((:instance mod-sum (a (bits a (1- i) 0)) (n (expt 2 i)))
                        (:instance mod-sum (a b) (b a) (n (expt 2 i))))
		  :nonlinearp t
		  :in-theory (enable bits-mod))))

(local-defthmd lza-special-28
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (g0 a b) i) 1))
	   (< (+ (bits a (1- i) 0) (bits b (1- i) 0)) (expt 2 i)))
  :hints (("Goal" :use (lza-special-15 (:instance lza-special-14 (j (1- i))))
                  :in-theory (enable p0-rewrite g0-rewrite))))

(local-defthmd lza-special-30
  (implies (and (not (zp n))
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (g0 a b) i) 1))
	   (equal (+ (bits a (1- i) 0) (bits b (1- i) 0))
	          (bits (+ a b) (1- i) 0)))
  :hints (("Goal" :use (lza-special-27 lza-special-28))))

(local-defthmd lza-special-31
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (g0 a b) i) 1))
	   (equal (+ (bits a (1- i) 0) (bits b (1- i) 0))
	          0))
  :hints (("Goal" :use (lza-special-30 (:instance bits-plus-mult-2 (x 0) (y 1) (k n) (n (1- i)) (m 0))))))

(local-defthmd lza-special-32
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (g0 a b) i) 1))
	   (equal (bitn (k0 a b n) (1- i))
	          1))
  :hints (("Goal" :use (lza-special-31
                        (:instance bitn-bits (x a) (i (1- i)) (j 0) (k (1- i)))
                        (:instance bitn-bits (x b) (i (1- i)) (j 0) (k (1- i))))
		  :in-theory (enable k0-rewrite))))
(local-defthmd lza-special-34
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n)
		(= (bitn (g0 a b) i) 1))
	   (inset a b n i))
  :hints (("Goal" :use (lza-special-32)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite inset))))

(local-defthmd lza-special-35
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i n))
	   (equal (bitn (w0 a b n) i)
	          0))
  :hints (("Goal" :use (lza-special-13 lza-special-20 lza-special-26 lza-special-34)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite))))

(local-defthmd lza-special-36
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(natp i)
		(< i n))
	   (equal (bits (w0 a b n) i 0)
	          1))
  :hints (("Goal" :induct (nats i))
          ("Subgoal *1/2" :use (lza-special-35 (:instance bitn-plus-bits (x (w0 a b n)) (n i) (m 0))))
	  ("Subgoal *1/1" :use (lza-special-12))))

(defthmd lza-thm-1-case-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n)))
	   (equal (w0 a b n)
	          1))
  :hints (("Goal" :use ((:instance lza-special-36 (i (1- n))))
                  :in-theory (enable w0))))

;;----------------------------------------------------------------------------------------

(defund u0 (x y n)
  (bits (logior x (lognot y)) (- n 2) 0))

(local-defthm lza0-1
  (implies (and (not (zp n))
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2)))
	   (and (>= x (expt 2 (1- n)))
		(<= y (1- (expt 2 (1- n))))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :use (expo-lower-bound (:instance expo-upper-bound (x y))))))

(local-defthmd lza0-2
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2)))
	   (iff (= (- x y) 1)
	        (and (= x (expt 2 (1- n)))
		     (= y (1- (expt 2 (1- n)))))))
  :hints (("Goal" :nonlinearp t :use (lza0-1))))

(local-defthmd lza0-3
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(= (expo x) (1- n)))
	   (iff (= x (expt 2 (1- n)))
	        (= (bits x (- n 2) 0) 0)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (expo-upper-bound
		        (:instance bitn-0-1 (n (1- n)))
		        (:instance bitn-expt (n (1- n)))
		        (:instance bitn-plus-bits (n (1- n)) (m 0))))))

(local-defthmd lza0-4
  (implies (and (natp n)
                (> n 1)
                (natp y)
		(= (expo y) (- n 2)))
	   (iff (= y (1- (expt 2 (1- n))))
	        (= (bits (lognot y) (- n 2) 0) 0)))
  :hints (("Goal" :in-theory (enable bits-lognot bvecp)
                  :use ((:instance expo-upper-bound (x y))))))

(local-defthmd lza0-5
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2)))
	   (iff (and (= (bits x (- n 2) 0) 0)
	             (= (bits (lognot y) (- n 2) 0) 0))
	        (equal (u0 x y n) 0)))
  :hints (("Goal" :in-theory (enable u0 bits-logior))))

(defthmd lza-thm-0-a
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2)))
	   (iff (equal (- x y) 1)
	        (equal (u0 x y n) 0)))
  :hints (("Goal" :use (lza0-2 lza0-3 lza0-4 lza0-5)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd lza0-6
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(not (= (u0 x y n) 0)))
	   (equal (fl (/ (u0 x y n) (expt 2 (1+ (expo (u0 x y n))))))
	          0))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance expo-upper-bound (x (u0 x y n)))))))

(local-defthmd lza0-7
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(not (= (u0 x y n) 0)))
	   (equal (bits (u0 x y n) (- n 2) (1+ (expo (u0 x y n))))
	          0))
  :hints (("Goal" :nonlinearp t
                  :use (lza0-6 (:instance bits-shift-down-1 (x (u0 x y n)) (k (1+ (expo (u0 x y n)))) (i (- n (+ (expo (u0 x y n)) 3))) (j 0))))))

(local-defthmd lza0-8
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y))
           (>= (expo (u0 x y n)) 0))
  :hints (("Goal" :in-theory (enable u0)
                  :use ((:instance expo-monotone (x 1) (y (u0 x y n)))))))

(local-defthmd lza0-9
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y))
           (<= (expo (u0 x y n)) (- n 2)))
  :hints (("Goal" :in-theory (enable u0)
                  :use ((:instance expo<= (x (u0 x y n)) (n (- n 2)))
		        (:instance bits-bounds (x (logior x (lognot y))) (i (- n 2)) (j 0))))))

(local-defthmd lza0-10
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(not (= (u0 x y n) 0)))
	   (and (equal (bits x (- n 2) (1+ (expo (u0 x y n))))
	               0)
		(equal (bits (lognot y) (- n 2) (1+ (expo (u0 x y n))))
	               0)))
  :hints (("Goal" :nonlinearp t
                  :use (lza0-7 lza0-8)
		  :in-theory (enable bits-bits bits-logior u0))))

(local-defthmd lza0-11
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(not (= (u0 x y n) 0)))
	   (equal (+ (expt 2 (1- n)) (bits x (- n 2) 0))
	          x))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (expo-upper-bound expo-lower-bound
		        (:instance bits-bounds (i (- n 2)) (j 0))
		        (:instance bitn-0-1 (n (1- n)))
		        (:instance bitn-expt (n (1- n)))
		        (:instance bitn-plus-bits (n (1- n)) (m 0))
			(:instance bits-plus-bits (n (- n 2)) (p (1+ (expo (u0 x y n)))) (m 0))))))

(local-defthmd lza0-12
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(not (= (u0 x y n) 0))
		(not (= (expo (u0 x y n)) (- n 2))))
	   (equal (bits x (- n 2) 0)
	          (bits x (expo (u0 x y n)) 0)))
  :hints (("Goal" :use (lza0-8 lza0-9 lza0-10 (:instance bits-plus-bits (n (- n 2)) (p (1+ (expo (u0 x y n)))) (m 0))))))

(local-defthmd lza0-13
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(not (= (u0 x y n) 0)))
	   (equal (+ (expt 2 (1- n)) (bits x (expo (u0 x y n)) 0))
	          x))
  :hints (("Goal" :use (lza0-11 lza0-12))))

(local-defthmd lza0-14
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(not (= (u0 x y n) 0)))
	   (equal (bits y (- n 2) (1+ (expo (u0 x y n))))
	          (1- (expt 2 (- n (+ (expo (u0 x y n)) 2))))))
  :hints (("Goal" :use (lza0-8 lza0-9 lza0-10)
                  :cases ((= (expo (u0 x y n)) (- n 2)))
                  :in-theory (enable bits-lognot))))

(local-defthmd lza0-15
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
	   (equal (+ (expt 2 (1- n))
	             (- (expt 2 (1+ (expo (u0 x y n)))))
		     (bits y (expo (u0 x y n)) 0))
	          y))
  :hints (("Goal" :use (lza0-8 lza0-9 lza0-14
                        (:instance expo-upper-bound (x y))
			(:instance bits-plus-bits (x y) (n (- n 2)) (p (1+ (expo (u0 x y n)))) (m 0)))
                  :cases ((= (expo (u0 x y n)) (- n 2)))
                  :in-theory (enable bvecp))))

(local-defthmd lza0-16
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
	   (equal (- x y)
	          (+ (expt 2 (1+ (expo (u0 x y n))))
		     (- (bits x (expo (u0 x y n)) 0)
		        (bits y (expo (u0 x y n)) 0)))))
  :hints (("Goal" :use (lza0-13 lza0-15))))

(local-defthmd lza0-16
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
	   (equal (- x y)
	          (+ (expt 2 (1+ (expo (u0 x y n))))
		     (- (bits x (expo (u0 x y n)) 0)
		        (bits y (expo (u0 x y n)) 0)))))
  :hints (("Goal" :use (lza0-13 lza0-15))))

(local-defthmd lza0-17
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
	   (< (- x y)
	      (expt 2 (+ 2 (expo (u0 x y n))))))
  :hints (("Goal" :nonlinearp t
                  :use (lza0-16 lza0-8 lza0-9
                        (:instance bits-bounds (i (expo (u0 x y n))) (j 0))
			(:instance bits-bounds (x y) (i (expo (u0 x y n))) (j 0))))))

;; This should be in bits.lisp:

(defthmd bitn-expo
  (implies (not (zp x))
           (equal (bitn x (expo x)) 1))
  :hints (("Goal" :use (expo-upper-bound expo-lower-bound
                        (:instance expo>= (n 0))
                        (:instance bvecp-bitn-2 (n (1+ (expo x))) (k (expo x))))
		  :in-theory (enable bvecp)
                  :nonlinearp t)))

(local-defthmd lza0-18
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
	   (equal (bitn (u0 x y n) (expo (u0 x y n)))
	          1))
  :hints (("Goal" :in-theory (enable bitn-expo))))

(local-defthmd lza0-19
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
           (>= (- (bitn x (expo (u0 x y n)))
	          (bitn y (expo (u0 x y n))))
	       0))
  :hints (("Goal" :use (lza0-18 lza0-8 lza0-9
                        (:instance bitn-lognot (x y) (n (expo (u0 x y n))))
			(:instance bitn-0-1 (n (expo (u0 x y n))))
			(:instance bitn-0-1 (x (lognot y)) (n (expo (u0 x y n))))
			(:instance bitn-0-1 (x y) (n (expo (u0 x y n)))))
		  :in-theory (enable bits-logior bitn-bits bitn-logior u0))))

(local-defthmd lza0-20
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
           (> (- x y)
	      (expt 2 (expo (u0 x y n)))))
  :hints (("Goal" :nonlinearp t
                  :use (lza0-16 lza0-19 lza0-8 lza0-9
			(:instance bitn-0-1 (n (expo (u0 x y n))))
			(:instance bitn-0-1 (x y) (n (expo (u0 x y n))))
			(:instance bitn-plus-bits (n (expo (u0 x y n))) (m 0))
			(:instance bitn-plus-bits (x y) (n (expo (u0 x y n))) (m 0))
                        (:instance bits-bounds (i (1- (expo (u0 x y n)))) (j 0))
			(:instance bits-bounds (x y) (i (1- (expo (u0 x y n)))) (j 0))))))

(defthmd lza-thm-0-b
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
           (and (<= (expo (u0 x y n)) (expo (- x y)))
	        (<= (expo (- x y)) (1+ (expo (u0 x y n))))))
  :hints (("Goal" :use (lza0-17 lza0-20 lza0-8 lza0-9
			(:instance expo<= (x (- x y)) (n (1+ (expo (u0 x y n)))))
			(:instance expo>= (x (- x y)) (n (expo (u0 x y n))))))))

