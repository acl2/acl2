(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "basic")
(include-book "bits")
(include-book "log")
(include-book "float")
(include-book "add")
(include-book "ppa")

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)|
                                |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
				simplify-products-gather-exponents-equal mod-cancel-*-const
				cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)|
				|(equal x (if a b c))| |(equal (if a b c) x)| mod-theorem-one-b))

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

(defund z1 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (logior (logand (logxor (bits (p0 a b) n 1) (k0 a b n))
		  (logxor (p0 a b) (* 2 (k0 a b n))))
	  (logand (logxor (bits (p0 a b) n 1) (g0 a b))
		  (logxor (p0 a b) (* 2 (g0 a b))))))

(defund w1 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (bits (lognot (z1 a b n)) (- n 2) 0))

(local-defun assumps (a b n)
  (and (not (zp n))
       (bvecp a n)
       (bvecp b n)
       (= (bitn (p0 a b) (1- n)) 1)
       (> (+ a b) (expt 2 n))))

(local-defthmd bvecp-w1
  (implies (assumps a b n)
           (bvecp (w1 a b n) (1- n)))
  :hints (("Goal" :in-theory (enable w1 z1))))

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

(local-defthmd z1-rewrite
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
                (not (zp j))
		(< j (1- n)))
	   (equal (bitn (z1 a b n) j)
	          (if (or (and (not (= (bitn (p0 a b) (1+ j)) (bitn (k0 a b n) j)))
			       (not (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j)))))
			  (and (not (= (bitn (p0 a b) (1+ j)) (bitn (g0 a b) j)))
			       (not (= (bitn (p0 a b) j) (bitn (g0 a b) (1- j))))))
		      1 0)))
  :hints (("Goal" :in-theory (enable z1 bitn-bits bitn-logxor bitn-logior bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x (p0 a b)))
		        (:instance bitn-0-1 (n (1+ j)) (x (p0 a b)))
			(:instance bitn-0-1 (n j) (x (k0 a b n)))
			(:instance bitn-0-1 (n (1- j)) (x (k0 a b n)))
			(:instance bitn-0-1 (n j) (x (g0 a b)))
			(:instance bitn-0-1 (n (1- j)) (x (g0 a b)))
			(:instance bitn-shift-up (x (k0 a b n)) (k 1) (n (1- j)))
			(:instance bitn-shift-up (x (g0 a b)) (k 1) (n (1- j)))))))

(defthmd w1-rewrite
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
                (not (zp j))
		(< j (1- n)))
	   (equal (bitn (w1 a b n) j)
	          (if (and (or (= (bitn (p0 a b) (1+ j)) (bitn (k0 a b n) j))
		               (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j))))
			   (or (= (bitn (p0 a b) (1+ j)) (bitn (g0 a b) j))
			       (= (bitn (p0 a b) j) (bitn (g0 a b) (1- j)))))
		      1 0)))
  :hints (("Goal" :in-theory (enable w1 bitn-bits z1-rewrite)
                  :use ((:instance bitn-0-1 (n j) (x (p0 a b)))
		        (:instance bitn-0-1 (n (1+ j)) (x (p0 a b)))
			(:instance bitn-0-1 (n j) (x (k0 a b n)))
			(:instance bitn-0-1 (n (1- j)) (x (k0 a b n)))
			(:instance bitn-0-1 (n j) (x (g0 a b)))
			(:instance bitn-0-1 (n (1- j)) (x (g0 a b)))
			(:instance bitn-lognot (x (z1 a b n)) (n j))))))

(local-defund conds (a b n j)
  (and (= (bits (w1 a b n) (- n 2) (1+ j)) 0)
       (= (bits (+ a b) (1- n) (1+ j)) 0)
       (or (>= (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))
           (= (bitn (k0 a b n) j) 1))))

(local-defund goal (a b n)
  (and (>= (w1 a b n) 2)
       (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w1 a b n)))
           (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w1 a b n)))))))

(local-defthmd  bitn-w1-1
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (equal (bitn (+ a b) (1+ j)) 0))
  :hints (("Goal" :in-theory (enable conds)
                  :use ((:instance bitn-bits (x (+ a b)) (i (1- n)) (j (1+ j)) (k 0))))))

(local-defthmd  bitn-w1-2
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (iff (= (bitn (p0 a b) (1+ j)) 1)
	        (>= (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable p0 bitn-logxor gen-val)
                  :use (bitn-w1-1
		        (:instance bitn-0-1 (x a) (n (1+ j)))
		        (:instance bitn-0-1 (x b) (n (1+ j)))
		        (:instance ripple-carry-lemma (x a) (y b) (i (1+ j)) (cin 0))
		        (:instance cbit-rewrite (x a) (y b) (i j) (cin 0))))))

(local-defthmd  bitn-w1-3
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (iff (= (bitn (k0 a b n) j) 0)
	        (>= (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable conds k0-rewrite)
                  :nonlinearp t
                  :use ((:instance bitn-0-1 (x a) (n j))
		        (:instance bitn-0-1 (x b) (n j))
		        (:instance bitn-plus-bits (x a) (n j) (m 0))
		        (:instance bitn-plus-bits (x b) (n j) (m 0))
		        (:instance bits-bounds (x a) (i (1- j)) (j 0))
		        (:instance bits-bounds (x b) (i (1- j)) (j 0))))))

(local-defthmd  bitn-w1-4
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (iff (= (bitn (k0 a b n) j) 0)
	        (= (bitn (p0 a b) (1+ j)) 1)))
  :hints (("Goal" :use (bitn-w1-2 bitn-w1-3))))

(local-defthmd  bitn-w1-5
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (equal (bitn (w1 a b n) j)
	          (if (and (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j)))
			   (or (= (bitn (p0 a b) (1+ j)) (bitn (g0 a b) j))
			       (= (bitn (p0 a b) j) (bitn (g0 a b) (1- j)))))
		      1 0)))
  :hints (("Goal" :use (bitn-w1-4) :in-theory (enable w1-rewrite))))

(local-defthmd  bitn-w1-6
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (implies (= (bitn (p0 a b) j) 1)
	            (>= (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable conds p0-rewrite k0-rewrite))))

(local-defthmd  bitn-w1-7
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (implies (= (bitn (p0 a b) j) 1)
	            (= (bitn (k0 a b n) (1- j)) 0)))
  :hints (("Goal" :in-theory (enable p0-rewrite k0-rewrite)
                  :nonlinearp t
                  :use (bitn-w1-6
		        (:instance bitn-0-1 (x a) (n j))
		        (:instance bitn-0-1 (x b) (n j))
		        (:instance bitn-0-1 (x a) (n (1- j)))
		        (:instance bitn-0-1 (x b) (n (1- j)))
		        (:instance bitn-plus-bits (x a) (n j) (m 0))
		        (:instance bitn-plus-bits (x b) (n j) (m 0))
		        (:instance bitn-plus-bits (x a) (n (1- j)) (m 0))
		        (:instance bitn-plus-bits (x b) (n (1- j)) (m 0))
		        (:instance bits-bounds (x a) (i (- j 2)) (j 0))
		        (:instance bits-bounds (x b) (i (- j 2)) (j 0))))))

(local-defthmd  bitn-w1-8
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j) (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j))))
           (and (equal (bitn (p0 a b) j) 0)
	        (equal (bitn (k0 a b n) (1- j)) 0)))
  :hints (("Goal" :use (bitn-w1-7 (:instance bitn-0-1 (x (p0 a b)) (n j)) (:instance bitn-0-1 (x (k0 a b n)) (n (1- j)))))))

(local-defthmd  bitn-w1-9
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j) (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j))))
           (equal (bitn (p0 a b) (1+ j)) (bitn (g0 a b) j)))
  :hints (("Goal" :use (bitn-w1-4 bitn-w1-8) :in-theory (enable p0-rewrite g0-rewrite k0-rewrite))))

(local-defthmd  bitn-w1
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j))
           (equal (bitn (w1 a b n) j)
                  (if (equal (bitn (p0 a b) j) (bitn (k0 a b n) (1- j)))
		      1 0)))
  :hints (("Goal" :use (bitn-w1-9) :in-theory (enable bitn-w1-5))))

(local-defthmd base-case-1
  (implies (assumps a b n)
           (> (+ (bits a (- n 2) 0) (bits b (- n 2) 0))
	      (expt 2 (1- n))))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x a) (n (1- n)) (m 0))
                        (:instance bitn-plus-bits (x b) (n (1- n)) (m 0))
			(:instance bitn-0-1 (x a) (n (1- n)))
			(:instance bitn-0-1 (x b) (n (1- n))))
		  :in-theory (enable p0-rewrite)
		  :nonlinearp t)))

(local-defthmd base-case-2
  (implies (assumps a b n)
           (< (+ a b) (+ (expt 2 n) (expt 2 (1- n)))))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x a) (n (1- n)) (m 0))
                        (:instance bitn-plus-bits (x b) (n (1- n)) (m 0))
			(:instance bitn-0-1 (x a) (n (1- n)))
			(:instance bitn-0-1 (x b) (n (1- n)))
			(:instance bits-bounds (x a) (i (- n 2)) (j 0))
			(:instance bits-bounds (x b) (i (- n 2)) (j 0)))
		  :in-theory (enable p0-rewrite)
		  :nonlinearp t)))

(local-defthmd base-case-3
  (implies (assumps a b n)
           (< (bits (+ a b) (1- n) 0)
	      (expt 2 (1- n))))
  :hints (("Goal" :in-theory (e/d (bits-mod) (ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  :use (base-case-2
                        (:instance mod-force (a 1) (m (+ a b)) (n (expt 2 n)))))))

(local-defthmd base-case-4
  (implies (assumps a b n)
           (equal (bitn (+ a b) (1- n)) 0))
  :hints (("Goal" :use (base-case-3
                        (:instance bitn-0-1 (x (+ a b)) (n (1- n)))
			(:instance bitn-plus-bits (x (+ a b)) (n (1- n)) (m 0))))))
			
(local-defthm base-case
  (implies (assumps a b n) (conds a b n (- n 2)))
  :hints (("Goal" :in-theory (enable conds)
                  :use (base-case-1 base-case-4))))

(local-defthmd conds-0-0
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
                 :use (conds-0-0
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

(local-defthmd w1-1-1
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j) (= (bitn (w1 a b n) j) 1))
           (equal (expo (w1 a b n)) j))
  :hints (("Goal" :in-theory (enable conds bvecp)
                  :nonlinearp t
                  :use (bvecp-w1
                        (:instance expo>= (x (w1 a b n)) (n j))
			(:instance expo<= (x (w1 a b n)) (n j))
			(:instance bitn-plus-bits (x (w1 a b n)) (n j) (m 0))
			(:instance bits-plus-bits (x (w1 a b n)) (n (- n 2)) (p (1+ j)) (m 0))
			(:instance bits-bounds (x (w1 a b n)) (i (1- j)) (j 0))))))

(local-defthmd w1-1-3
  (implies (and (assumps a b n) (not (zp j)) (< j (1- n)) (conds a b n j) (= (bitn (w1 a b n) j) 1))
           (not (= (bitn (p0 a b) j) 1)))
  :hints (("Goal" :use ( bitn-w1
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

(local-defthmd w1-1-4
  (implies (and (natp a) (natp b) (natp j))
           (equal (bits (+ a b) j 0)
                  (mod (+ (bits a j 0) (bits b j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use ((:instance mod-sum (n (expt 2 (1+ j))) (a a) (b b))
		        (:instance mod-sum (n (expt 2 (1+ j))) (b a) (a (mod b (expt 2 (1+ j)))))))))

(local-defthmd w1-1-5
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
                  :in-theory (enable w1-1-4 p0-rewrite))))

(local-defthmd w1-1-6
  (implies (and (assumps a b n)
                (not (zp j))
		(< j (1- n))
		(conds a b n j)
		(= (bitn (w1 a b n) j) 1)
		(= (bitn (p0 a b) j) 0))
           (equal (bits (+ a b) (1- n) 0)
	          (+ (bits a (1- j) 0) (bits b (1- j) 0))))
  :hints (("Goal" :use ((:instance bits-plus-bits (x (+ a b)) (n (1- n)) (p (1+ j)) (m 0)))
                  :in-theory (enable w1-1-5 conds))))

(local-defthmd w1-1-7
  (implies (and (assumps a b n)
                (not (zp j))
		(< j (1- n))
		(conds a b n j)
		(= (bitn (w1 a b n) j) 1)
		(= (bitn (p0 a b) j) 0))
           (and (>= (expo (bits (+ a b) (1- n) 0)) (1- j))
	        (<= (expo (bits (+ a b) (1- n) 0)) j)))
  :hints (("Goal" :use ( bitn-w1 w1-1-6 (:instance bitn-0-1 (x a) (n j))
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
                  :in-theory (enable p0-rewrite k0-rewrite))))

(local-defthmd w1-1
  (implies (and (assumps a b n)
                (not (zp j))
		(< j (1- n))
		(conds a b n j)
		(= (bitn (w1 a b n) j) 1))
           (goal a b n))
  :hints (("Goal" :use (w1-1-3 w1-1-7
                        (:instance bvecp-bitn-0 (x (w1 a b n)) (n j))
                        (:instance bitn-0-1 (x (p0 a b)) (n j)))
		  :nonlinearp t
                  :in-theory (e/d (bvecp goal w1-1-1) (bvecp-bitn-0)))))

(local-defthmd w1-0-1
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (equal (bits (w1 a b n) (- n 2) j) 0))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w1 a b n)) (n (- n 2)) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w1-0-2
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
	       (expt 2 j)))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w1 a b n)) (n (- n 2)) (m j))
                        (:instance bitn-plus-bits (x a) (n j) (m 0))
                        (:instance bitn-plus-bits (x b) (n j) (m 0))
			(:instance bitn-0-1 (x a) (n j))
			(:instance bitn-0-1 (x b) (n j)))
		  :nonlinearp t
                  :in-theory (enable conds p0-rewrite k0-rewrite))))

(local-defthm w1-0-3
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (or (= (bitn (k0 a b n) (1- j)) 1)
	       (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w1-0-2  bitn-w1)
                  :in-theory (enable conds p0-rewrite k0-rewrite)))); w1-rewrite))))

(local-defthm w1-0-4
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (or (= (bitn (k0 a b n) (1- j)) 1)
	       (>= (+ (bits a (1- j) 0) (bits b (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w1-0-2  bitn-w1)
                  :in-theory (enable conds p0-rewrite k0-rewrite)))); w1-rewrite))))

(local-in-theory (disable ACL2::|(mod (+ x y) z) where (<= 0 z)|))

(local-defthmd w1-0-5
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (equal (bits (+ a b) j 0)
	          (mod (+ (expt 2 j) (bits a (1- j) 0) (bits b (1- j) 0))
		       (expt 2 (1+ j)))))
  :hints (("Goal" :use (w1-0-2
                        (:instance bitn-plus-bits (x a) (n j) (m 0))
                        (:instance bitn-plus-bits (x b) (n j) (m 0))
                        (:instance bitn-0-1 (x a) (n j))
                        (:instance bitn-0-1 (x b) (n j)))
                  :in-theory (enable w1-1-4 p0-rewrite))))

(local-defthmd w1-0-6
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (equal (bits (+ a b) j 0)
                  (mod (- (+ (bits a (1- j) 0) (bits b (1- j) 0)) (expt 2 j)) (expt 2 (1+ j)))))
  :hints (("Goal" :use (w1-0-5  bitn-w1
                        (:instance mod-mult (m (- (+ (bits a (1- j) 0) (bits b (1- j) 0)) (expt 2 j)))
			                    (n (expt 2 (1+ j)))
					    (a 1)))
		  ;:nonlinearp t
                  :in-theory (enable p0-rewrite k0-rewrite))))

(local-defthm w1-0-7
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0)
		(= (bitn (p0 a b) j) 1))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w1-0-2 w1-0-6
			(:instance bits-bounds (x a) (i (1- j)) (j 0))
			(:instance bits-bounds (x b) (i (1- j)) (j 0)))
		  :nonlinearp t)))

(local-defthm w1-0-8
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0)
		(= (bitn (p0 a b) j) 0)
		(= (bitn (k0 a b n) j) 1))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use ( bitn-w1
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
		  :nonlinearp t
                  :in-theory (enable w1-1-4 p0-rewrite k0-rewrite))))

(local-defthm w1-0-9
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0)
		(= (bitn (p0 a b) j) 0)
		(= (bitn (k0 a b n) j) 0))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use ( bitn-w1
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
		  :nonlinearp t
                  :in-theory (enable w1-1-4 p0-rewrite k0-rewrite))))

(local-defthm w1-0-10
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (< (bits (+ a b) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w1-0-7 w1-0-8 w1-0-9)
                  :in-theory (enable p0-rewrite k0-rewrite))))

(local-defthm w1-0-11
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (equal (bitn (+ a b) j) 0))
  :hints (("Goal" :use (w1-0-10
                        (:instance bitn-0-1 (x (+ a b)) (n j))
                        (:instance bitn-plus-bits (x (+ a b)) (n j) (m 0))))))

(local-defthm w1-0-12
  (implies (and (natp a)
                (natp b)
		(not (zp n))
		(not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (equal (bits (+ a b) (1- n) j) 0))
  :hints (("Goal" :use (w1-0-11 (:instance bits-plus-bitn (x (+ a b)) (n (1- n)) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w1-0
  (implies (and (assumps a b n)
                (not (zp j))
		(< j (1- n))
		(assumps a b n)
		(conds a b n j)
		(= (bitn (w1 a b n) j) 0))
           (conds a b n (1- j)))
  :hints (("Goal" :use (w1-0-1 w1-0-4 w1-0-12)
                  :in-theory (enable conds))))

(local-defthm conds-goal
  (implies (and (natp j) (< j (1- n)) (conds a b n j) (assumps a b n))
           (goal a b n))
  :rule-classes ()
  :hints (("Goal" :induct (nats j))
          ("Subgoal *1/2" :use (w1-1 w1-0 (:instance bitn-0-1 (x (w1 a b n)) (n j))))))

(local-defthm assumps-goal
  (implies (assumps a b n) (goal a b n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance conds-goal (j (- n 2)))))))

(local-defthm lza-thm-2-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (> (+ a b) (expt 2 n)))
           (and (>= (w1 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w1 a b n)))))))
  :rule-classes ()
  :hints (("Goal" :use assumps-goal :in-theory (enable goal))))

;;----------------------------------------------------------------------------------------

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

(local-defthmd lza-cor-2-1
  (implies (assumps a b n)
           (< (bits (+ a b 1) (1- n) 0)
	      (expt 2 (1- n))))
  :hints (("Goal" :in-theory (enable bitn-logxor bits-mod p0)
                  :nonlinearp t
                  :use ((:instance bitn-plus-bits (x a) (n (1- n)) (m 0))
		        (:instance bitn-plus-bits (x b) (n (1- n)) (m 0))
			(:instance bitn-0-1 (x a) (n (1- n)))
			(:instance bitn-0-1 (x b) (n (1- n)))
			(:instance mod-force (a 1) (n (expt 2 n)) (m (+ a b 1)))
			(:instance bits-bounds (x a) (i (- n 2)) (j 0))
			(:instance bits-bounds (x b) (i (- n 2)) (j 0))))))

(local-defthmd lza-cor-2
  (implies (assumps+ a b n)
	   (and (not (zp (e a b n)))
	        (< (e a b n) (1- n))))
  :hints (("Goal" :use (lza-cor-1 lza-cor-2-1
			(:instance expo-monotone (x 2) (y (bits (+ 1 a b) (+ -1 n) 0)))
			(:instance expo<= (x (bits (+ 1 a b) (+ -1 n) 0)) (n (- n 2)))
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
  (implies (and (assumps+ a b n)  (< (e a b n) (1- n)))
	   (equal (bitn (w1 a b n) (e a b n)) 1))
  :hints (("Goal"  :in-theory (enable w1-rewrite p0 k0 g0 bitn-logxor bitn-logior bitn-logand bitn-bits)
                   :use (lza-cor-23 lza-cor-24 lza-cor-2
		         (:instance bitn-0-1 (x a) (n (e a b n)))
			 (:instance bitn-0-1 (x b) (n (e a b n)))
		         (:instance bitn-0-1 (x a) (n (1- (e a b n))))
			 (:instance bitn-0-1 (x b) (n (1- (e a b n))))
			 (:instance bitn-0-1 (x (lognot a)) (n (e a b n)))
			 (:instance bitn-0-1 (x (lognot b)) (n (e a b n)))
		         (:instance bitn-0-1 (x (lognot a)) (n (1- (e a b n))))
			 (:instance bitn-0-1 (x (lognot b)) (n (1- (e a b n))))
			 (:instance bitn-lognot (x a) (n (e a b n)))
			 (:instance bitn-lognot (x b) (n (e a b n)))
			 (:instance bitn-lognot (x a) (n (1- (e a b n))))
			 (:instance bitn-lognot (x b) (n (1- (e a b n))))))))

(local-defthmd lza-cor-27
  (implies (assumps+ a b n)
	   (>= (expo (w1 a b n)) (e a b n)))
  :hints (("Goal"  :in-theory (enable bvecp)
                   :use (lza-cor-26 lza-cor-2
		         (:instance expo>= (x (w1 a b n)) (n (e a b n)))))))

(local-defthmd lza-cor-28
  (implies (assumps+ a b n)
	   (equal (expo (bits (+ a b) (1- n) 0))
	          (1- (e a b n))))
  :hints (("Goal"  :nonlinearp t
                   :use (lza-cor-2 lza-cor-4
                         (:instance expo-unique (x (bits (+ a b) (1- n) 0)) (n (1- (e a b n))))))))

(defthm lza-thm-2-case-3
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (> (+ a b) (expt 2 n)))
           (and (>= (w1 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w1 a b n)))))
                (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w1 a b n)))))))
  :rule-classes ()
  :hints (("Goal" :use (lza-thm-2-1 lza-cor-27 lza-cor-28))))

;;----------------------------------------------------------------------------------------

(defund c (x n) (bits (lognot x) (1- n) 0))

(local-defthm bvecp-c
  (implies (and (not (zp n))
                (bvecp x n))
	   (bvecp (c x n) n))
  :hints (("Goal" :in-theory (enable c))))

(local-defthm bitn-c
  (implies (and (not (zp n))
                (bvecp x n)
		(natp k)
		(< k n))
	   (equal (bitn (c x n) k)
	          (if (= (bitn x k) 1) 0 1)))
  :hints (("Goal" :in-theory (enable c bitn-bits)
                  :use ((:instance bitn-0-1 (n k))
		        (:instance bitn-0-1 (n k) (x (lognot x)))
			(:instance bitn-lognot (n k))))))

(local-defthm flip-c
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(natp k)
		(< k n))
	   (and (equal (bitn (p0 (c a n) (c b n)) k)
	               (bitn (p0 a b) k))
		(equal (bitn (k0 (c a n) (c b n) n) k)
	               (bitn (g0 a b) k))
                (equal (bitn (g0 (c a n) (c b n)) k)
	               (bitn (k0 a b n) k))))
  :hints (("Goal" :use ((:instance bitn-0-1 (x a) (n k))
		        (:instance bitn-0-1 (x b) (n k)))
		  :in-theory (enable p0-rewrite k0-rewrite g0-rewrite))))

(local-defthm bvecp-p0
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
	   (and (bvecp (p0 a b) n)
	        (bvecp (g0 a b) n)
		(bvecp (k0 a b n) n)))
  :hints (("Goal" :in-theory (enable p0 k0 g0))))

(local-defthmd bitn-bvecp-0
  (implies (and (natp m)
                (<= n m)
		(natp n)
		(bvecp x n))
	   (equal (bitn x m) 0))
  :hints (("Goal" :in-theory (enable bvecp))))                

(local-defthm flip-p0
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
	   (equal (p0 (c a n) (c b n))
	          (p0 a b)))
  :hints (("Goal" :use ((:instance bit-diff-diff (x (p0 a b)) (y (p0 (c a n) (c b n))))
                        (:instance bitn-bvecp-0 (m (BIT-DIFF (P0 A B) (P0 (C A N) (C B N)))) (x (p0 a b)))
			(:instance bitn-bvecp-0 (m (BIT-DIFF (P0 A B) (P0 (C A N) (C B N)))) (x (p0 (c a n) (c b n))))))))

(local-defthm flip-g0
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
	   (equal (g0 (c a n) (c b n))
	          (k0 a b n)))	          
  :hints (("Goal" :use ((:instance bit-diff-diff (x (k0 a b n)) (y (g0 (c a n) (c b n))))
                        (:instance bitn-bvecp-0 (m (BIT-DIFF (k0 A B n) (G0 (C A N) (C B N)))) (x (k0 a b n)))
			(:instance bitn-bvecp-0 (m (BIT-DIFF (k0 A B n) (G0 (C A N) (C B N)))) (x (g0 (c a n) (c b n))))))))

(local-defthm flip-k0
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
	   (equal (k0 (c a n) (c b n) n)
	          (g0 a b)))	          
  :hints (("Goal" :use ((:instance bit-diff-diff (x (g0 a b)) (y (k0 (c a n) (c b n) n)))
                        (:instance bitn-bvecp-0 (m (BIT-DIFF (g0 A B) (k0 (C A N) (C B N) n))) (x (g0 a b)))
			(:instance bitn-bvecp-0 (m (BIT-DIFF (g0 A B) (k0 (C A N) (C B N) n))) (x (k0 (c a n) (c b n) n)))))))

(local-defthm w1-c
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
           (equal (w1 (c a n) (c b n) n)
	          (w1 a b n)))
  :hints (("Goal" :in-theory (enable w1 z1))))


(local-defthmd lza-flip-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (> (+ (c a n) (c b n)) (expt 2 n)))
  :hints (("Goal" :in-theory (enable bits-lognot c) :nonlinearp t)))

(local-defthm lza-flip-2
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (equal (+ (c a n) (c b n))
	          (+ (expt 2 n)
		     (bits (lognot (+ a b 1)) (1- n) 0))))
  :hints (("Goal" :in-theory (enable bvecp c bits-lognot)
                  :nonlinearp t)))

(local-defthm lza-flip-3
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (equal (+ (c a n) (c b n) 1)
	          (+ (expt 2 n)
		     (bits (lognot (+ a b)) (1- n) 0))))
  :hints (("Goal" :in-theory (enable bvecp c bits-lognot)
                  :nonlinearp t)))

(local-defthmd lza-flip-4
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (equal (bits (+ (c a n) (c b n)) (1- n) 0)
	          (bits (lognot (+ a b 1)) (1- n) 0)))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use (lza-flip-2)
		  :nonlinearp t)))

(local-defthmd lza-flip-5
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (equal (bits (+ (c a n) (c b n) 1) (1- n) 0)
	          (bits (lognot (+ a b)) (1- n) 0)))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use (lza-flip-3)
		  :nonlinearp t)))
		        
(defthm lza-thm-2-case-4
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (and (>= (w1 a b n) 2)
                (or (= (expo (bits (lognot (+ a b)) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (lognot (+ a b)) (1- n) 0)) (1- (expo (w1 a b n)))))
                (or (= (expo (bits (lognot (+ a b 1)) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (lognot (+ a b 1)) (1- n) 0)) (1- (expo (w1 a b n)))))))
  :rule-classes ()
  :hints (("Goal" :use (lza-flip-1 lza-flip-4 lza-flip-5
                        (:instance lza-thm-2-case-3 (a (c a n)) (b (c b n)))))))

;;----------------------------------------------------------------------------------------

(local-defthmd lza-special-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n))))
	   (equal (bits (p0 a b) (1- n) 0)
	          (1- (expt 2 n))))
  :hints (("Goal" :in-theory (enable p0)
                  :use ((:instance lutz-lemma (x a) (y b))))))

(local-defthmd lza-special-2
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(natp i)
		(< i n))
	   (equal (bitn (p0 a b) i) 1))
  :hints (("Goal" :in-theory (enable p0)
                  :use (lza-special-1
		        (:instance bvecp-bitn-2 (k i) (x (bits (p0 a b) (1- n) 0)))))))

(local-defthmd lza-special-3
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(natp i)
		(< i n))
	   (and (equal (bitn (k0 a b n) i) 0)
	        (equal (bitn (g0 a b) i) 0)))
  :hints (("Goal" :use (lza-special-2)
		  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite))))

(local-defthmd lza-special-4
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(not (zp i))
		(< i (1- n)))
	   (equal (bitn (w1 a b n) i) 0))
  :hints (("Goal" :in-theory (enable lza-special-2 lza-special-3 w1-rewrite bitn-bits bitn-logxor bitn-logand bitn-logior))))

(local-defthmd lza-special-5
  (implies (and (not (zp n))
                (> n 1)
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n))))
	   (equal (bitn (z1 a b n) 0) 1))
  :hints (("Goal" :in-theory (enable lza-special-2 lza-special-3 z1 bitn-bits bitn-logxor bitn-logand bitn-logior)
                  :use ((:instance bitn-shift-up (x (g0 a b)) (k 1) (n -1))
		        (:instance bitn-shift-up (x (k0 a b n)) (k 1) (n -1))))))

(local-defthmd  lza-special-6
  (implies (and (not (zp n))
                (> n 1)
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n))))
	   (equal (bitn (w1 a b n) 0) 0))
  :hints (("Goal" :in-theory (enable lza-special-5 w1 bitn-bits)
                  :use ((:instance bitn-lognot (n 0) (x (z1 a b n)))))))

(local-defthmd  lza-special-7
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(natp i)
		(>= i (1- n)))
	   (equal (bitn (w1 a b n) i) 0))
  :hints (("Goal" :in-theory (enable w1))))

(local-defthmd lza-special-8
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(natp i))
	   (equal (bitn (w1 a b n) i) 0))
  :hints (("Goal" :use (lza-special-4 lza-special-6 lza-special-7))))

(defthmd lza-thm-2-case-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(natp i))
	   (equal (w1 a b n) 0))
  :hints (("Goal" :in-theory (enable lza-special-8)
                  :use ((:instance bit-diff-diff (x (w1 a b n)) (y 0))))))

;;----------------------------------------------------------------------------------------

(local-defthmd lza-special-9
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n))
 	   (equal (bitn (z1 a b n) 0)
	          (if (and (= (bitn (p0 a b) 0) 1)
		           (= (bitn (p0 a b) 1) 1))
		      1 0)))
  :hints (("Goal" :use ((:instance bitn-shift-up (x (g0 a b)) (k 1) (n -1))
		        (:instance bitn-shift-up (x (k0 a b n)) (k 1) (n -1)))
	          :in-theory (enable z1 bitn-bits bitn-logior bitn-logxor bitn-logand p0-rewrite g0-rewrite k0-rewrite))))

(local-defthmd lza-special-10
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n))
 	   (equal (bitn (w1 a b n) 0)
	          (if (and (= (bitn (p0 a b) 0) 1)
		           (= (bitn (p0 a b) 1) 1))
		      0 1)))
  :hints (("Goal" :use ((:instance bitn-lognot (x (z1 a b n)) (n 0)))
	          :in-theory (enable w1 bitn-bits lza-special-9))))

(local-defthmd lza-special-11
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(or (= (+ a b) (expt 2 n))
		    (= (+ a b) (- (expt 2 n) 2))))
 	   (equal (bitn a 0) (bitn b 0)))
  :hints (("Goal" :use (mod-plus-mod-2 (:instance mod012 (m a)) (:instance mod012 (m b)))
	          :in-theory (e/d (bitn-rec-0 bits-mod) (ACL2::|(mod x 2)|)))))

(local-defthmd lza-special-12
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(or (= (+ a b) (expt 2 n))
		    (= (+ a b) (- (expt 2 n) 2))))
 	   (equal (bitn (w1 a b n) 0)
	          1))
  :hints (("Goal" :use (lza-special-11)
	          :in-theory (enable lza-special-10 p0-rewrite))))

(defund s1us2 (a b n i)
  (or (and (= (bitn (p0 a b) (1+ i)) 1) (= (bitn (p0 a b) i) 1) (= (bitn (p0 a b) (1- i)) 1))
      (and (= (bitn (p0 a b) (1+ i)) 1) (= (bitn (p0 a b) i) 1) (= (bitn (g0 a b) (1- i)) 1))
      (and (= (bitn (p0 a b) (1+ i)) 1) (= (bitn (g0 a b) i) 1) (= (bitn (k0 a b n) (1- i)) 1))
      (and (= (bitn (g0 a b) (1+ i)) 1) (= (bitn (k0 a b n) i) 1) (= (bitn (k0 a b n) (1- i)) 1))
      (and (= (bitn (k0 a b n) (1+ i)) 1) (= (bitn (k0 a b n) i) 1) (= (bitn (k0 a b n) (1- i)) 1))
      (and (= (bitn (p0 a b) (1+ i)) 1) (= (bitn (p0 a b) i) 1) (= (bitn (k0 a b n) (1- i)) 1))
      (and (= (bitn (p0 a b) (1+ i)) 1) (= (bitn (k0 a b n) i) 1) (= (bitn (g0 a b) (1- i)) 1))
      (and (= (bitn (k0 a b n) (1+ i)) 1) (= (bitn (g0 a b) i) 1) (= (bitn (g0 a b) (1- i)) 1))
      (and (= (bitn (g0 a b) (1+ i)) 1) (= (bitn (g0 a b) i) 1) (= (bitn (g0 a b) (1- i)) 1))))

(local-defthmd lza-special-13
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(not (zp i))
		(< i (1- n))
		(s1us2 a b n i))
	   (equal (bitn (w1 a b n) i)
	          0))
  :hints (("Goal" :in-theory (enable s1us2 w1-rewrite p0-rewrite k0-rewrite g0-rewrite))))

(local-defthmd lza-special-14
  (implies (and (natp n)
                (> n 1)
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
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(natp i)
		(< i n))
	   (equal (bitn (+ a b) i)
	          0))		  
  :hints (("Goal" :in-theory (enable bitn-expt-0))))

(local-defthmd lza-special-16
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (>= (+ (bits a (1- i) 0) (bits b (1- i) 0))
	       (expt 2 i)))
  :hints (("Goal" :use (lza-special-15 (:instance lza-special-14 (j (1- i)))))))

(local-defthmd lza-special-17
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
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

(local-defthmd lza-special-18
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (>= (+ (bits a i 0) (bits b i 0))
	       (expt 2 (1+ i))))
  :hints (("Goal" :in-theory (enable p0-rewrite)
                  :nonlinearp t
                  :use (lza-special-16
                        (:instance bitn-plus-bits (x a) (n i) (m 0))
                        (:instance bitn-plus-bits (x b) (n i) (m 0))
                        (:instance bitn-0-1 (x a) (n i))
                        (:instance bitn-0-1 (x b) (n i))))))

(local-defthmd lza-special-19
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (equal (bitn (p0 a b) (1+ i))
	          1))
  :hints (("Goal" :use (lza-special-18 (:instance lza-special-14 (j i)) (:instance lza-special-15 (i (1+ i)))))))

(local-defthmd lza-special-20
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (s1us2 a b n i))
  :hints (("Goal" :use (lza-special-17 lza-special-19)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite s1us2))))

(local-defthmd lza-special-21
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n)))
	   (equal (mod (+ (bits a i 0) (bits b i 0)) (expt 2 (1+ i)))
	          (bits (+ a b) i 0)))
  :hints (("Goal" :use ((:instance mod-sum (a (bits a i 0)) (n (expt 2 (1+ i))))
                        (:instance mod-sum (a b) (b a) (n (expt 2 (1+ i)))))
		  :nonlinearp t
		  :in-theory (enable bits-mod))))

(local-defthmd lza-special-22
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
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
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (k0 a b n) i) 1))
	   (equal (+ (bits a i 0) (bits b i 0))
	          0))
  :hints (("Goal" :use (lza-special-22 (:instance bits-plus-mult-2 (x 0) (y 1) (k n) (n i) (m 0))))))

(local-defthmd lza-special-24
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (k0 a b n) i) 1))
	   (equal (bitn (k0 a b n) (1- i))
	          1))
  :hints (("Goal" :use (lza-special-23
                        (:instance bitn-bits (x a) (j 0) (k (1- i)))
                        (:instance bitn-bits (x b) (j 0) (k (1- i))))
		  :in-theory (enable k0-rewrite))))

(local-defthmd lza-special-25
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (k0 a b n) i) 1))
	   (equal (bitn (p0 a b) (1+ i))
	          0))
  :hints (("Goal" :use (lza-special-23
                        (:instance lza-special-15 (i (1+ i)))
			(:instance lza-special-14 (j i))))))
			
(local-defthmd lza-special-26
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (k0 a b n) i) 1))
	   (s1us2 a b n i))
  :hints (("Goal" :use (lza-special-24 lza-special-25)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite s1us2))))

(local-defthmd lza-special-27
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n)))
	   (equal (mod (+ (bits a (1- i) 0) (bits b (1- i) 0)) (expt 2 i))
	          (bits (+ a b) (1- i) 0)))
  :hints (("Goal" :use ((:instance mod-sum (a (bits a (1- i) 0)) (n (expt 2 i)))
                        (:instance mod-sum (a b) (b a) (n (expt 2 i))))
		  :nonlinearp t
		  :in-theory (enable bits-mod))))

(local-defthmd lza-special-28
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (< (+ (bits a (1- i) 0) (bits b (1- i) 0)) (expt 2 i)))
  :hints (("Goal" :use (lza-special-15 (:instance lza-special-14 (j (1- i))))
                  :in-theory (enable p0-rewrite g0-rewrite))))

(local-defthmd lza-special-30
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (equal (+ (bits a (1- i) 0) (bits b (1- i) 0))
	          (bits (+ a b) (1- i) 0)))
  :hints (("Goal" :use (lza-special-27 lza-special-28))))

(local-defthmd lza-special-31
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (equal (+ (bits a (1- i) 0) (bits b (1- i) 0))
	          0))
  :hints (("Goal" :use (lza-special-30 (:instance bits-plus-mult-2 (x 0) (y 1) (k n) (n (1- i)) (m 0))))))

(local-defthmd lza-special-32
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (equal (bitn (k0 a b n) (1- i))
	          1))
  :hints (("Goal" :use (lza-special-31
                        (:instance bitn-bits (x a) (i (1- i)) (j 0) (k (1- i)))
                        (:instance bitn-bits (x b) (i (1- i)) (j 0) (k (1- i))))
		  :in-theory (enable k0-rewrite))))

(local-defthmd lza-special-33
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (equal (bitn (p0 a b) (1+ i))
	          1))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x a) (n i) (m 0))
                        (:instance bitn-plus-bits (x b) (n i) (m 0))
                        (:instance lza-special-15 (i (1+ i)))
			(:instance lza-special-14 (j i)))
		  :in-theory (enable g0-rewrite))))
			
(local-defthmd lza-special-34
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (s1us2 a b n i))
  :hints (("Goal" :use (lza-special-32 lza-special-33)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite s1us2))))

(local-defthmd lza-special-35
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(not (zp i))
		(< i (1- n)))
	   (equal (bitn (w1 a b n) i)
	          0))
  :hints (("Goal" :use (lza-special-13 lza-special-20 lza-special-26 lza-special-34)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite))))

(local-defthmd lza-special-36
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n))
		(natp i)
		(< i (1- n)))
	   (equal (bits (w1 a b n) i 0)
	          1))
  :hints (("Goal" :induct (nats i))
          ("Subgoal *1/2" :use (lza-special-35 (:instance bitn-plus-bits (x (w1 a b n)) (n i) (m 0))))
	  ("Subgoal *1/1" :use (lza-special-12))))

(local-defthmd lza-thm-2-case-2-a
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n)))
	   (equal (w1 a b n)
	          1))
  :hints (("Goal" :use ((:instance lza-special-36 (i (- n 2))))
                  :in-theory (enable w1))))

(local-defthmd lza-special-37
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i n))
	   (equal (bitn (+ a b) i)
	          1))		  
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable bvecp)
                  :use ((:instance bvecp-bitn-2 (x (+ a b)) (k i))))))

(local-defthmd lza-special-38
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2)))
	   (equal (bitn (+ a b) 0)
	          0))		  
  :hints (("Goal" :use ((:instance bitn-shift-up (x (1- (expt 2 (1- n)))) (n -1) (k 1))))))

(local-defthmd lza-special-39
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i n))
           (iff (= (bitn (p0 a b) i) 1)
	        (< (+ (bits a (1- i) 0) (bits b (1- i) 0))
	           (expt 2 i))))
  :hints (("Goal" :use (lza-special-37 (:instance lza-special-14 (j (1- i)))))))

(local-defthmd lza-special-40
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (equal (bitn (g0 a b) (1- i)) 0))
  :hints (("Goal" :in-theory (enable g0-rewrite)
                  :nonlinearp t
                  :use (lza-special-39
                        (:instance bitn-plus-bits (x a) (n (1- i)) (m 0))
                        (:instance bitn-plus-bits (x b) (n (1- i)) (m 0))
                        (:instance bitn-0-1 (x a) (n (1- i)))
                        (:instance bitn-0-1 (x b) (n (1- i)))))))

(local-defthmd lza-special-41
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (< (+ (bits a i 0) (bits b i 0))
	      (expt 2 (1+ i))))
  :hints (("Goal" :in-theory (enable p0-rewrite)
                  :nonlinearp t
                  :use (lza-special-39
                        (:instance bitn-plus-bits (x a) (n i) (m 0))
                        (:instance bitn-plus-bits (x b) (n i) (m 0))
                        (:instance bitn-0-1 (x a) (n i))
                        (:instance bitn-0-1 (x b) (n i))))))

(local-defthmd lza-special-42
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (equal (bitn (p0 a b) (1+ i))
	          1))
  :hints (("Goal" :use (lza-special-41 (:instance lza-special-14 (j i)) (:instance lza-special-37 (i (1+ i)))))))

(local-defthmd lza-special-43
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 1))
	   (s1us2 a b n i))
  :hints (("Goal" :use (lza-special-40 lza-special-42)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite s1us2))))

(local-defthmd lza-special-44
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (p0 a b) i) 0))
	   (equal (bitn (g0 a b) (1- i)) 1))
  :hints (("Goal" :use (lza-special-39
			(:instance lza-special-39 (i (1- i)))
			(:instance bitn-0-1 (x a) (n (1- i)))
			(:instance bitn-0-1 (x b) (n (1- i)))
			(:instance bits-bounds (x a) (i (- i 2)) (j 0))
			(:instance bits-bounds (x b) (i (- i 2)) (j 0))
			(:instance bitn-plus-bits (x a) (n (1- i)) (m 0))
			(:instance bitn-plus-bits (x b) (n (1- i)) (m 0)))
	          :nonlinearp t
                  :in-theory (enable p0-rewrite g0-rewrite))))

(local-defthmd lza-special-45
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (k0 a b n) i) 1))
	   (equal (bitn (p0 a b) (1+ i)) 1))
  :hints (("Goal" :use ((:instance lza-special-39 (i (1+ i)))
			(:instance bitn-0-1 (x a) (n i))
			(:instance bitn-0-1 (x b) (n i))
			(:instance bits-bounds (x a) (i (1- i)) (j 0))
			(:instance bits-bounds (x b) (i (1- i)) (j 0))
			(:instance bitn-plus-bits (x a) (n i) (m 0))
			(:instance bitn-plus-bits (x b) (n i) (m 0)))
	          :nonlinearp t
                  :in-theory (enable k0-rewrite))))

(local-defthmd lza-special-46
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (k0 a b n) i) 1))
	   (s1us2 a b n i))
  :hints (("Goal" :use (lza-special-44 lza-special-45)
	   :in-theory (enable p0-rewrite g0-rewrite k0-rewrite s1us2))))

(local-defthmd lza-special-47
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (equal (bitn (p0 a b) (1+ i)) 0))
  :hints (("Goal" :use ((:instance lza-special-39 (i (1+ i)))
			(:instance bitn-0-1 (x a) (n i))
			(:instance bitn-0-1 (x b) (n i))
			(:instance bitn-plus-bits (x a) (n i) (m 0))
			(:instance bitn-plus-bits (x b) (n i) (m 0)))
	          :nonlinearp t
                  :in-theory (enable g0-rewrite))))

(local-defthmd lza-special-48
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n))
		(= (bitn (g0 a b) i) 1))
	   (s1us2 a b n i))
  :hints (("Goal" :use (lza-special-44 lza-special-47)
	   :in-theory (enable p0-rewrite g0-rewrite k0-rewrite s1us2))))

(local-defthmd lza-special-49
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(not (zp i))
		(< i (1- n)))
	   (equal (bitn (w1 a b n) i)
	          0))
  :hints (("Goal" :use (lza-special-13 lza-special-43 lza-special-46 lza-special-48)
                  :in-theory (enable p0-rewrite g0-rewrite k0-rewrite))))

(local-defthmd lza-special-50
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2))
		(natp i)
		(< i (1- n)))
	   (equal (bits (w1 a b n) i 0)
	          1))
  :hints (("Goal" :induct (nats i))
          ("Subgoal *1/2" :use (lza-special-49 (:instance bitn-plus-bits (x (w1 a b n)) (n i) (m 0))))
	  ("Subgoal *1/1" :use (lza-special-12))))

(local-defthmd lza-thm-2-case-2-b
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (- (expt 2 n) 2)))
	   (equal (w1 a b n)
	          1))
  :hints (("Goal" :use ((:instance lza-special-50 (i (- n 2))))
	   :in-theory (enable w1))))

(defthmd lza-thm-2-case-2
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(or (= (+ a b) (expt 2 n))
		    (= (+ a b) (- (expt 2 n) 2))))
	   (equal (w1 a b n)
	          1))
  :hints (("Goal" :use (lza-thm-2-case-2-a lza-thm-2-case-2-b))))
