(in-package "RTL")

(include-book "../rel9-rtl-pkg/lib/util")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "basic")
(include-book "bits")
(include-book "log")
(include-book "float")

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)|
                          |(mod (+ x (mod a b)) y)|
                          simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                          ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| mod-theorem-one-b))

(local-defun s (a b) (+ a b))

(local-defun assumps (a b n)
  (and (not (zp n))
       (bvecp a n)
       (bvecp b n)
       (> (s a b) (expt 2 n))))

(defund p0 (a b) (logxor a b))

(defund k0 (a b n) (logand (bits (lognot a) (1- n) 0) (bits (lognot b) (1- n) 0)))

(defund w0 (a b n)
  (bits (lognot (logxor (p0 a b) (* 2 (k0 a b n)))) (1- n) 0))

(local-defthmd bvecp-w0
  (implies (assumps a b n)
           (bvecp (w0 a b n) n))
  :hints (("Goal" :in-theory (enable w0))))

(local-defthmd p0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(integerp j))
	   (equal (bitn (p0 a b) j)
	          (if (= (bitn a j) (bitn b j))
		      0 1)))
  :hints (("Goal" :in-theory (enable p0 bitn-logxor)
                  :use ((:instance bitn-0-1 (x a) (n j))
		        (:instance bitn-0-1 (x b) (n j))))))

(local-defthmd k0-rewrite
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

(local-defthmd w0-rewrite
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
       (= (bits (s a b) (1- n) (1+ j)) 0)
       (or (>= (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))
           (= (bitn (k0 a b n) j) 1))))

(local-defund goal (a b n)
  (and (>= (w0 a b n) 2)
       (or (= (expo (bits (s a b) (1- n) 0)) (expo (w0 a b n)))
           (= (expo (bits (s a b) (1- n) 0)) (1- (expo (w0 a b n)))))))

(local-defthm conds-127
  (implies (assumps a b n) (conds a b n (1- n)))
  :hints (("Goal" :in-theory (enable assumps conds s))))

(local-defthmd s-127-0
  (implies (assumps a b n)
           (not (equal (bits (s a b) (1- n) 0) 0)))
  :hints (("Goal" :in-theory (enable bvecp) :nonlinearp t
                  :use ((:instance bitn-plus-bits (x (+ a b)) (m 0))
		        (:instance bitn-0-1 (x (+ a b)))))))

(local-defthmd conds-0-1
  (implies (and (assumps a b n) (conds a b n 0))
           (equal (bitn (s a b) 0) 1))
  :hints (("Goal" :in-theory (enable assumps conds)
                 :use (s-127-0
		       (:instance bitn-0-1 (x (s a b)) (n 0))
                       (:instance bits-plus-bitn (x (s a b)) (n (1- n)) (m 0))))))

(local-defthmd conds-0-2
  (implies (and (assumps a b n) (conds a b n 0))
           (equal (bitn (s a b) 0)
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
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 1) (= (bitn (p0 a b) j) 0))
           (equal (bits (s a b) (1- n) 0)
	          (+ (bits a (1- j) 0) (bits b (1- j) 0))))
  :hints (("Goal" :use ((:instance bits-plus-bits (x (s a b)) (n (1- n)) (p (1+ j)) (m 0)))
                  :in-theory (enable w0-1-5 conds))))

(local-defthmd w0-1-7
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 1) (= (bitn (p0 a b) j) 0))
           (and (>= (expo (bits (s a b) (1- n) 0)) (1- j))
	        (<= (expo (bits (s a b) (1- n) 0)) j)))
  :hints (("Goal" :use (w0-1-6 (:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j))
			(:instance bitn-0-1 (x a) (n (1- j)))
                        (:instance bitn-0-1 (x b) (n (1- j)))
			(:instance bitn-plus-bits (x a) (n (1- j)) (m 0))
			(:instance bitn-plus-bits (x b) (n (1- j)) (m 0))
			(:instance bits-bounds (x a) (i (- j 2)) (j 0))
			(:instance bits-bounds (x b) (i (- j 2)) (j 0))
			(:instance expo>= (x (bits (s a b) (1- n) 0)) (n (1- j)))
			(:instance expo<= (x (bits (s a b) (1- n) 0)) (n j)))
		  :nonlinearp t
                  :in-theory (enable w0-rewrite p0-rewrite k0-rewrite))))

(local-defthmd w0-1
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 1))
           (goal a b n))
  :hints (("Goal" :use (w0-1-3 w0-1-7
                        (:instance bvecp-bitn-0 (x (w0 a b n)) (n j))
                        (:instance bitn-0-1 (x (p0 a b)) (n j)))
		  :nonlinearp t
                  :in-theory (e/d (bvecp goal w0-1-1) (bvecp-bitn-0)))))

(local-defthmd w0-0-1
  (implies (and (integerp a) (integerp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
           (equal (bits (w0 a b n) (1- n) j) 0))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w0 a b n)) (n (1- n)) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w0-0-2
  (implies (and (integerp a) (integerp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0) (= (bitn (p0 a b) j) 1))
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
  (implies (and (integerp a) (integerp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
           (or (= (bitn (k0 a b n) (1- j)) 1)
	       (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-2)
                  :in-theory (enable conds p0-rewrite k0-rewrite w0-rewrite))))

(local-defthm w0-0-4
  (implies (and (integerp a) (integerp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
           (or (= (bitn (k0 a b n) (1- j)) 1)
	       (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-2)
                  :in-theory (enable conds p0-rewrite k0-rewrite w0-rewrite))))

(local-in-theory (disable ACL2::|(mod (+ x y) z) where (<= 0 z)|))

(local-defthmd w0-0-5
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0) (= (bitn (p0 a b) j) 1))
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
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0) (= (bitn (p0 a b) j) 1))
           (equal (bits (+ a b) j 0)
                  (mod (- (+ (bits a (1- j) 0) (bits b (1- j) 0)) (expt 2 j)) (expt 2 (1+ j)))))
  :hints (("Goal" :use (w0-0-5
                        (:instance mod-mult (m (- (+ (bits a (1- j) 0) (bits b (1- j) 0)) (expt 2 j)))
			                    (n (expt 2 (1+ j)))
					    (a 1)))
		  ;:nonlinearp t
                  :in-theory (enable w0-rewrite p0-rewrite k0-rewrite))))

(local-defthm w0-0-7
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0) (= (bitn (p0 a b) j) 1))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-2 w0-0-6
			(:instance bits-bounds (x a) (i (1- j)) (j 0))
			(:instance bits-bounds (x b) (i (1- j)) (j 0)))
		  :nonlinearp t)))

(local-defthm w0-0-8
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0) (= (bitn (p0 a b) j) 0) (= (bitn (k0 a b n) j) 1))
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
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b
  n j) (= (bitn (w0 a b n) j) 0) (= (bitn (p0 a b) j) 0) (= (bitn (k0 a b n) j) 0))
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
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w0-0-7 w0-0-8 w0-0-9)
                  :in-theory (enable p0-rewrite k0-rewrite))))

(local-defthm w0-0-11
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
           (equal (bitn (+ a b) j) 0))
  :hints (("Goal" :use (w0-0-10
                        (:instance bitn-0-1 (x (+ a b)) (n j))
                        (:instance bitn-plus-bits (x (+ a b)) (n j) (m 0))))))

(local-defthm w0-0-12
  (implies (and (natp a) (natp b) (not (zp n)) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
           (equal (bits (+ a b) (1- n) j) 0))
  :hints (("Goal" :use (w0-0-11 (:instance bits-plus-bitn (x (+ a b)) (n (1- n)) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w0-0
  (implies (and (assumps a b n) (not (zp j)) (< j n) (conds a b n j) (= (bitn (w0 a b n) j) 0))
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
