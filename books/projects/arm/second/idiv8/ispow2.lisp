(IN-PACKAGE "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)|
                          |(mod (+ x (mod a b)) y)| simplify-products-gather-exponents-equal mod-cancel-*-const
			  cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)| |(equal x (if a b c))|
			  |(equal (if a b c) x)| |(logior 1 x)| MOD-THEOREM-ONE-B |(mod (- x) y)|))

(include-book "idiv8")

;;-------------------------------------------------------------------------------------------------------------

;; We shall prove (xor-pow2) that if x is a 64-bit vector and k is an integer, then
;;
;;   2^(64) - x = 2^k <=> (2x)[64:0] ^ x = 2^k.
;;
;; This requires the following lemma (bits-shift-equal): If n >= m and x[n:m+1] = x[n-1:m], then
;;
;;   x[n:m] = 2^(n-m+1) * x[n].

(local-defthmd bits-shift-equal-1
  (implies (and (integerp x)
                (natp n)
		(natp m)
		(> n m)
		(= (bits x n (1+ m)) (bits x (1- n) m)))
	   (and (equal (bits x n m) (+ (* (bitn x n) (expt 2 (- n m))) (bits x (1- n) m)))
	        (equal (bitn x n) (bitn x (1- n)))
		(equal (bits x (1- n) (1+ m)) (bits x (- n 2) m))))
  :hints (("Goal" :in-theory (disable bits-bits)
	          :use (bitn-plus-bits
		        (:instance bitn-bits (i n) (j (1+ m)) (k (1- (- n m))))
	                (:instance bitn-bits (i (1- n)) (j m) (k (1- (- n m))))
		        (:instance bits-bits (i n) (j (1+ m)) (k (- (- n m) 2)) (l 0))
			(:instance bits-bits (i (1- n)) (j m) (k (- (- n m) 2)) (l 0))))))

(local-defthmd bits-shift-equal-2
  (implies (and (integerp x)
                (natp n)
		(natp m)
		(> n m)
	        (equal (bitn x n) (bitn x (1- n)))
		(equal (bits x (1- n) (1+ m)) (bits x (- n 2) m))
		(equal (bits x (1- n) m) (* (1- (expt 2 (- n m))) (bitn x (1- n)))))
	   (equal (+ (* (bitn x n) (expt 2 (- n m))) (bits x (1- n) m))
	          (* (1- (* 2 (expt 2 (- n m))))
		     (bitn x n))))
  :hints (("Goal" :in-theory (disable acl2::normalize-factors-gather-exponents))))

(local-defthmd bits-shift-equal
  (implies (and (integerp x)
                (natp n)
		(natp m)
		(>= n m)
		(= (bits x n (1+ m)) (bits x (1- n) m)))
	   (equal (bits x n m)
	          (* (1- (expt 2 (1+ (- n m))))
		     (bitn x n))))
  :hints (("Goal" :induct (nats n))
          ("Subgoal *1/2" :use (bits-shift-equal-1 bits-shift-equal-2))))

;;-----------------------

(local-defthmd xor-pow2-1
  (implies (natp k)
           (and (equal (bits (expt 2 k) (1- k) 0) 0)
	        (equal (bits (expt 2 k) 63 (1+ k)) 0)))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use ((:instance bits-shift-up-1 (x 1) (i 63) (j (1+ k)))
                        (:instance bits-shift-up-1 (x 1) (i (1- k)) (j 0))
			(:instance bits-plus-bitn (x 1) (n (- 63 k)) (m 0))))))

(local-defthmd xor-pow2-2
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64)
		(= (logxor (bits (* 2 x) 63 0) x) (expt 2 k)))
	   (and (equal (logxor (bits (* 2 x) (1- k) 0)
	                       (bits x (1- k) 0))
		       0)
		(equal (logxor (bits (* 2 x) 63 (1+ k))
	                       (bits x 63 (1+ k)))
		       0)))
  :hints (("Goal" :in-theory (enable bits-logxor)
                  :use (xor-pow2-1))))

(local-defthmd xor-pow2-3
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64)
		(= (logxor (bits (* 2 x) 63 0) x) (expt 2 k)))
	   (and (equal (bits (* 2 x) (1- k) 0)
	               (bits x (1- k) 0))
		(equal (bits (* 2 x) 63 (1+ k))
	               (bits x 63 (1+ k)))))
  :hints (("Goal" :in-theory (enable logxor-not-0)
                  :use (xor-pow2-2))))

(local-defthmd xor-pow2-4
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64)
		(equal (bits (* 2 x) (1- k) 0)
	               (bits x (1- k) 0)))
	   (equal (bits x (1- k) 0) 0))
  :hints (("Goal" :use ((:instance bits-shift-up-2 (k 1) (i (- k 2)))
                        (:instance bitn-plus-bits (n (1- k)) (m 0))
			(:instance bits-bounds (i (- k 2)) (j 0))
			(:instance bitn-0-1 (n (1- k)))))))

(local-defthmd xor-pow2-5
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64)
		(equal (bits (* 2 x) 63 (1+ k))
	               (bits x 63 (1+ k))))
	   (equal (bits x 63 k)
	          (* (1- (expt 2 (- 64 k)))
		     (bitn x 63))))
  :hints (("Goal" :use ((:instance bits-shift-up-1 (k 1) (i 63) (j (1+ k)))
                        (:instance bits-shift-equal (n 63) (m k))))))

(local-defthmd xor-pow2-6
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64)
		(= (logxor (bits (* 2 x) 63 0) x) (expt 2 k)))
	   (equal (- (expt 2 64) x)
	          (expt 2 k)))
  :hints (("Goal" :in-theory (enable xor-pow2-4 xor-pow2-5)
                  :use (xor-pow2-3
                        (:instance bits-plus-bits (n 63) (p k) (m 0))
			(:instance bitn-0-1 (n 63))))))

;; The converse of the preceding result is readily proved by exhaustive computation:

(local-defthmd xor-pow2-7
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64)
	        (= (- (expt 2 64) x) (expt 2 k)))
	  (equal (logxor (bits (* 2 x) 63 0) x)
	         (expt 2 k)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance bvecp-member (x k) (n 6))))))

(local-defthmd xor-pow2-8
  (implies (and (bvecp x 64)
                (natp k)
		(< k 64))
	   (iff (equal (- (expt 2 64) x)
	               (expt 2 k))
	        (equal (logxor (bits (* 2 x) 63 0) x)
	               (expt 2 k))))
  :hints (("Goal" :use (xor-pow2-6 xor-pow2-7))))

;; The constraints on k can be weakened:

(local-defthmd xor-pow2-9
  (implies (and (integerp k) (bvecp (expt 2 k) 64))
           (and (natp k) (< k 64))))

(local-defthmd xor-pow-10
  (implies (and (bvecp x 64)
                (> x 0))
	   (bvecp (- (expt 2 64) x) 64))
  :hints (("Goal" :in-theory (enable bvecp))))
	   
(local-defthmd xor-pow2
  (implies (and (bvecp x 64)
                (> x 0)
                (integerp k))
	   (iff (equal (- (expt 2 64) x)
	               (expt 2 k))
	        (equal (logxor (bits (* 2 x) 63 0) x)
	               (expt 2 k))))
  :hints (("Goal" :use (xor-pow2-8 xor-pow2-9 xor-pow-10))))

(local-defthmd xor-pow2-cor
  (implies (and (bvecp x 64)
                (> x 0))
	   (iff (equal (- (expt 2 64) x)
	               (expt 2 (expo (- (expt 2 64) x))))
	        (equal (bits (logxor (* 2 x) x) 63 0) 
	               (expt 2 (expo (bits (logxor (* 2 x) x) 63 0))))))
  :hints (("Goal" :in-theory (e/d (bits-logxor) (expo-2**n acl2::prefer-positive-addends-equal))
                  :use ((:instance expo-2**n (n (expo (logxor (bits (* 2 x) 63 0) x))))
                        (:instance expo-2**n (n (expo (- (expt 2 64) x))))
			(:instance xor-pow2 (k (expo (logxor (bits (* 2 x) 63 0) x))))
			(:instance xor-pow2 (k (expo (- (expt 2 64) x))))))))

;; The above result can be proved automatically by gl in .04 sec:

(gl::def-gl-rule xor-pow2-cor-gl
     :hyp
     (and (bvecp x 64) (> x 0))
     :concl
     (iff (equal (- (expt 2 64) x)
	         (expt 2 (expo (- (expt 2 64) x))))
	  (equal (bits (logxor (* 2 x) x) 63 0) 
	         (expt 2 (expo (bits (logxor (* 2 x) x) 63 0)))))
     :g-bindings (gl::auto-bindings (:nat x 64)))

;;----------------------------------------------------------------------------------------

;; After i iterations, z is conceptually split into 2^i segments of width w = 2^(6-i).
;; For 0 <= b < w, cntik(z, b, i, k) is the number of indices j, 0 <= j < k, such that
;; z[j] = 1 and j mod 2^{6-i) = b:

(local-defun cntik (z b i k)
  (if (zp k)
      0
    (if (and (= (bitn z (1- k)) 1)
             (= (mod (1- k) (expt 2 (- 6 i))) b))
	(1+ (cntik z b i (1- k)))
      (cntik z b i (1- k)))))

;; For 0 <= b < w, cntik(z, b, i) is the number of indices j, 0 <= j < 64, such that
;; z[j] = 1 and j mod 2^{6-i) = b:

(local-defund cnti (z b i)
  (cntik z b i 64))

;; cnti(z, b, i) satisfies the following recurrence relation:
;;   (a) cnti(z, b, 0) = z[b]
;;   (b) For i > 0, cnti(z, b, i) = cnti(z, b, i-1) + cnti(z, b+w, i-1)

(local-defthmd cntik-0
  (implies (and (bvecp z 64)
                (natp b)
		(< b 64)
                (natp k)
		(<= k 64))
	   (equal (cntik z b 0 k)
	          (if (and (= (bitn z b) 1)
		           (< b k))
		      1 0))))

(local-defthmd cnti-0
  (implies (and (bvecp z 64)
                (natp b)
		(< b 64))
	   (equal (cnti z b 0)
	          (bitn z b)))
  :hints (("Goal" :in-theory (enable cnti)
                  :use ((:instance cntik-0 (k 64))))))

(local-defthm mod-n-mod-2n
  (implies (and (not (zp n))
                (natp b)
		(< b n)
		(integerp k))
           (iff (= (mod k n) b)
	        (or (= (mod k (* 2 n)) b)
	            (= (mod k (* 2 n)) (+ b n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-equal-int (a k))
                        (:instance mod-def (x (/ (- k b) n)) (y 2))
			(:instance mod012 (m (/ (- k b) n)))
			(:instance mod-equal-int-reverse (a k) (n (* 2 n)))
			(:instance mod-equal-int-reverse (a k) (b (+ b n)) (n (* 2 n)))
			(:instance mod-of-mod (x k) (k 2))))))

(local-defthmd cntik-recurrence
  (implies (and (bvecp z 64)
                (not (zp i))
		(<= i 6)
		(natp b)
		(< b (expt 2 (- 6 i)))
		(natp k)
		(<= k 64))
	   (equal (cntik z b i k)
	          (+ (cntik z b (1- i) k)
		     (cntik z (+ b (expt 2 (- 6 i))) (1- i) k))))
  :hints (("Subgoal *1/9" :use ((:instance mod-n-mod-2n (k (1- k)) (n (expt 2 (- 6 i))))))
          ("Subgoal *1/5" :use ((:instance mod-n-mod-2n (k (1- k)) (n (expt 2 (- 6 i))))))))

(local-defthmd cnti-recurrence
  (implies (and (bvecp z 64)
                (not (zp i))
		(<= i 6)
		(natp b)
		(< b (expt 2 (- 6 i))))
	   (equal (cnti z b i)
	          (+ (cnti z b (1- i))
		     (cnti z (+ b (expt 2 (- 6 i))) (1- i)))))
  :hints (("Goal" :in-theory (enable cnti) :use (:instance cntik-recurrence (k 64)))))

;; cntk(z, k) is the number of set bits of z[k-1:0]:

(local-defun cntk (z k)
  (if (zp k)
      0
    (if (= (bitn z (1- k)) 1)
        (1+ (cntk z (1- k)))
      (cntk z (1- k)))))

;; cnt(z) is the number of set bits of z:

(local-defund cnt (z) (cntk z 64))

;; It is easy to prove that cnt(z) = cnti(z, 0, 6):

(local-defthmd cntk-cntik
  (implies (and (bvecp z 64)
		(natp k)
		(<= k 64))
           (equal (cntk z k)
	          (cntik z 0 6 k))))

(local-defthmd cnt-cnti
  (implies (bvecp z 64)
           (equal (cnt z)
	          (cnti z 0 6)))
  :hints (("Goal" :in-theory (enable cnt cnti cntk-cntik))))

;; z is a power of 2 <=> cnt(z) = 1:

(local-defthm cnt-1-pow2-1
  (implies (and (natp k)
                (natp e)
		(<= k e))
	   (equal (cntk (expt 2 e) k) 0))
  :hints (("Subgoal *1/5" :in-theory (enable bitn-expt-0))))

(local-defthmd cnt-1-pow2-2
  (implies (and (natp k)
                (natp e)
		(> k e))
	   (equal (cntk (expt 2 e) k) 1))	   
  :hints (("Subgoal *1/8" :in-theory (enable bitn-expt))
          ("Subgoal *1/5" :in-theory (enable bitn-expt-0) :cases ((= e (1- k))))))

(local-defthm cnt-1-pow2-3
  (implies (and (integerp k)
                (natp z))
	   (iff (equal (cntk z k) 0)
		(equal (bits z (1- k) 0) 0)))
  :hints (("Goal" :induct (cntk z k))  
          ("Subgoal *1/3" :use ((:instance bitn-plus-bits (x z) (n (1- k)) (m 0))))
          ("Subgoal *1/2" :use ((:instance bitn-plus-bits (x z) (n (1- k)) (m 0))))))

(local-defthmd cnt-1-pow2-4
  (implies (and (natp k)
                (natp z)
		(< z (expt 2 k))
	        (equal (cntk z k) 1))
           (equal (expt 2 (expo z))
	          z))		  
  :hints (("Subgoal *1/8" :in-theory (enable bvecp)
                          :use ((:instance bitn-plus-bits (x z) (n (1- k)) (m 0))
                                (:instance bits-bounds (x z) (i (- k 2)) (j 0))))				
          ("Subgoal *1/5" :in-theory (enable bvecp)
	                  :use ((:instance bitn-plus-bits (x z) (n (1- k)) (m 0))
			        (:instance expo-unique (x z) (n (1- k)))))				
          ("Subgoal *1/4" :in-theory (e/d (bvecp) (cnt-1-pow2-3))
	                  :use ((:instance bitn-plus-bits (x z) (n (1- k)) (m 0))
			        (:instance cnt-1-pow2-3 (k (1- k)))
			        (:instance expo-unique (x z) (n (1- k)))))))

(local-defthmd cnt-1-pow2
  (implies (bvecp z 64)
           (iff (= (cnt z) 1)
	        (= z (expt 2 (expo z)))))
  :hints (("Goal" :in-theory (enable bvecp cnt) :cases ((= z 0))
                  :use ((:instance cnt-1-pow2-2 (k 64) (e (expo z)))
		        (:instance expo<= (x z) (n 63))
			(:instance cnt-1-pow2-4 (k 64))))))

(local-defthmd cnti-1-pow2
  (implies (bvecp z 64)
           (iff (= (cnti z 0 6) 1)
	        (= z (expt 2 (expo z)))))
  :hints (("Goal" :use (cnt-cnti cnt-1-pow2))))

;;----------------------------------------------------------------------------------------

;; The invariant inv(z, i, w, a, v) is defined as follows:
;;
;;   (1) w = 2^(6-i)
;;
;;   (2) a[0], ..., a[i-1] and v are all natural numbers
;;
;;   (3) For all b, 0 <= b < w,
;;
;;       (a) cnti(z,b,i) = 0 => a[0][b] = ... = a[i-i][b] = 0
;;
;;       (b) cnti(z,b,i) = 1 <=> a[0][b] = ... = a[i-i][b] = 1
;;
;;       (c) cnti(z,b,i) > 0 <=> v[0][b] = 1

;; a[0], ..., a[i-1] are natural:

(local-defun all-natp (a i)
  (if (zp i)
      t
    (and (natp (ag (1- i) a))
         (all-natp a (1- i)))))

;; a[0][b] = ... = a[i-i][b] = 0:

(local-defun all-0 (a b i)
  (if (zp i)
      t
    (and (= (bitn (ag (1- i) a) b) 0)
         (all-0 a b (1- i)))))

;; a[0][b] = ... = a[i-i][b] = 1:

(local-defun all-1 (a b i)
  (if (zp i)
      t
    (and (= (bitn (ag (1- i) a) b) 1)
         (all-1 a b (1- i)))))

;; Part (3) of the invariant:

(local-defund inv-bit (z i a v b)
  (and (implies (= (cnti z b i) 0)
                (all-0 a b i))
       (iff (= (cnti z b i) 1)
            (all-1 a b i))
       (iff (> (cnti z b i) 0)
            (= (bitn v b) 1))))

(local-defun all-inv-bit (z i a v w)
  (if (zp w)
      t
    (and (inv-bit z i a v (1- w))
         (all-inv-bit z i a v (1- w)))))

;; The invariant"

(local-defund inv (z i w a v)
  (and (= w (expt 2 (- 6 i)))
       (natp v)
       (all-natp a i)
       (all-inv-bit z i a v w)))

;; Some obvious properties of the above recursive functions:

(local-defthmd all-natp-natp
  (implies (and (natp i) (natp j) (< j i)
                (all-natp a i))
           (natp (ag j a))))

(local-defthmd all-0-0
  (implies (and (natp i) (natp j) (< j i)
                (all-0 a b i))
           (equal (bitn (ag j a) b) 0)))

(local-defthmd all-1-1
  (implies (and (natp i) (natp j) (< j i)
                (all-1 a b i))
           (equal (bitn (ag j a) b) 1)))

(local-defthmd all-inv-bit-bit
  (implies (and (natp b) (natp w) (< b w)
                (all-inv-bit z i a v w))
           (inv-bit z i a v b)))

;;----------------------------------------------------------------------------------------

;; It will be convenient to use the following alternative definition of the main loop.
;; ispow2-loop-2, which allows us to hide the body of the loop:

(local-defund loop-2-body (i w a v)
  (LET* ((W (FLOOR W 2))
         (A (ISPOW2-LOOP-1 0 I W A))
         (A (AS I
                     (BITS (LOGXOR V (ASH V (- W)))
                           63 0)
                     A))
         (V (BITS (LOGIOR V (ASH V (- W)))
                      63 0)))
    (mv w a v)))

(local-defun ispow2-loop-2-alt (i w a v)
  (declare (xargs :measure (nfix (- 6 i))))
  (if (and (integerp i) (< i 6))
      (mv-let (w a v) (loop-2-body i w a v)
        (ispow2-loop-2-alt (+ i 1) w a v))
    (mv w a v)))

(local-defthmd loop-2-rewrite
  (equal (ispow2-loop-2 i w a v)
         (ispow2-loop-2-alt i w a v))
  :hints (("Goal" :in-theory (enable ispow2-loop-2 loop-2-body))))

;;----------------------------------------------------------------------------------------

;; We prove that the invariant holds after the first iteration of the loop:

(local-defthmd loop-2-init-1
  (implies (bvecp z 64)
           (mv-let (w a v) (loop-2-body 0 64 () z)
	     (declare (ignore w))
             (implies (and (natp b) (< b 32))
		      (and (= (bitn (ag 0 a) b)
		              (logxor (bitn z b) (bitn z (+ b 32))))
		           (= (bitn v b)
		              (logior (bitn z b) (bitn z (+ b 32))))))))
  :hints (("Goal" :in-theory (enable loop-2-body bitn-bits bitn-logxor bitn-logior)
                  :use ((:instance bitn-shift-down (x z) (k 32) (i b))))))

(local-defthmd loop-2-init-2
  (implies (bvecp z 64)
           (mv-let (w a v) (loop-2-body 0 64 () z)
	     (declare (ignore w))
             (implies (and (natp b) (< b 32))
		      (inv-bit z 1 a v b))))
  :hints (("Goal" :in-theory (enable all-1 all-0 cnti-0 inv-bit)
                  :use (loop-2-init-1
                        (:instance cnti-recurrence (i 1))
			(:instance bitn-0-1 (x z) (n b))
			(:instance bitn-0-1 (x z) (n (+ b 32)))))))

(local-defthmd loop-2-init-3
  (implies (bvecp z 64)
           (mv-let (w a v) (loop-2-body 0 64 () z)
	     (declare (ignore w))
	     (implies (and (natp u) (<= u 32))
	              (all-inv-bit z 1 a v u))))
  :hints (("Subgoal *1/8" :use ((:instance loop-2-init-2 (b (1- u)))))
          ("Subgoal *1/7" :use ((:instance loop-2-init-2 (b (1- u)))))
          ("Subgoal *1/6" :use ((:instance loop-2-init-2 (b (1- u)))))))

(local-defthmd loop-2-init
  (implies (bvecp z 64)
           (mv-let (w a v) (loop-2-body 0 64 () z)
             (inv z 1 w a v)))
  :hints (("Goal" :in-theory (enable loop-2-body inv)
                  :use ((:instance loop-2-init-3 (u 32))))))

;;----------------------------------------------------------------------------------------

;; Recurrence formulas for a[k][b] and v[b]:

(local-defthm ag-k-loop-1-1
  (implies (and (natp k) (natp j) (< k j))
           (equal (ag k (ispow2-loop-1 j i w a))
	          (ag k a)))
  :hints (("Goal" :in-theory (enable ispow2-loop-1))))

(local-defthm ag-k-loop-1
  (implies (and (natp i) (natp j) (natp k) (<= j k) (< k i))
           (equal (ag k (ispow2-loop-1 j i w a))
	          (bits (logior (ag k a) (ash (ag k a) (- w))) 63 0)))
  :hints (("Goal" :in-theory (enable ispow2-loop-1))
          ("Subgoal *1/1" :cases ((= k j)))))

(local-defthm hack-1
  (implies (and (natp i) (< i 6))
           (< (expt 2 (- 5 i)) 64))
  :rule-classes (:linear)
  :hints (("Goal" :nonlinearp t)))

(local-defthm bitn-a-k
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp k)
	   	           (< k i)
	    	           (natp b)
		           (< b w))
		      (equal (bitn (ag k a-next) b)
		             (logior (bitn (ag k a) b) (bitn (ag k a) (+ b w)))))))
  :hints (("Goal" :in-theory (enable inv bitn-bits bitn-logior loop-2-body)
                  :use ((:instance bitn-shift-down (k (expt 2 (- 5 i))) (i b) (x (ag k a)))
		        (:instance all-natp-natp (j k) (a a))))))

(local-defthm bitn-a-i
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v-next) (loop-2-body i w a v)
             (declare (ignore v-next))
	     (implies (and (natp b)
		           (< b w))
		      (equal (bitn (ag i a-next) b)
		             (logxor (bitn v b) (bitn v (+ b w)))))))
  :hints (("Goal" :in-theory (enable inv bitn-bits bitn-logxor bits-logxor loop-2-body)
                  :use ((:instance bitn-shift-down (k (expt 2 (- 5 i))) (i b) (x v))))))

(local-defthm bitn-v
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v-next) (loop-2-body i w a v)
             (declare (ignore a))
	     (implies (and (natp b)
		           (< b w))
		      (equal (bitn v-next b)
		             (logior (bitn v b) (bitn v (+ b w)))))))
  :hints (("Goal" :in-theory (enable inv bitn-bits bitn-logior bits-logxor loop-2-body)
                  :use ((:instance bitn-shift-down (k (expt 2 (- 5 i))) (i b) (x v))))))

;;----------------------------------------------------------------------------------------

;; We must prove that the invariant is preserved by loop-2-body.
;; (1) is quite trivial and (2) is not difficult:

(local-defthm natp-a-step-1
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore w v))
	     (implies (and (natp k)
	   	           (<= k i))
		      (natp (ag k a)))))
  :hints (("Goal" :in-theory (enable inv loop-2-body)
                  :cases ((= k i)))))

(local-defthm natp-a-step  
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore w v))
	     (implies (and (natp u)
	   	           (<= u (1+ i)))
		      (all-natp a u))))
  :hints (("Goal" :induct (nats u))
          ("Subgoal *1/2" :use ((:instance natp-a-step-1 (k (1- u)))))))


;; The proof of (3) consists of 3 cases:
;;
;;  Case 1: cnti(z, b + 2^(5-i), i) = 0
;;
;;  Case 2: cnti(z, b, i) = 0
;;
;;  Case 3: cnti(z, b + 2^(5-i), i) > 0 and cnti(z, b, i) > 0

(local-defthm case-1-1
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp k)
	   	           (< k i)
	    	           (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (equal (bitn (ag k a-next) b)
		             (bitn (ag k a) b)))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-a-k
                        (:instance all-inv-bit-bit (b (+ b (/ w 2))))
			(:instance all-0-0 (j k) (b (+ b (/ w 2))))))))

(local-defthm case-1-2
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp j)
	   	           (<= j i)
	    	           (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (iff (all-1 a b j)
		           (all-1 a-next b j)))))
  :hints (("Goal" :induct (all-1 a b j))))

(local-defthm case-1-3
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (iff (= (cnti z b (1+ i)) 1)
		           (all-1 a b i)))))		           
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (all-inv-bit-bit
                        (:instance case-1-2 (j i))
                        (:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-1-4
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v-next) (loop-2-body i w a v)
             (declare (ignore v-next))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (equal (bitn (ag i a) b)
		             (bitn v b)))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-a-i		  
                        (:instance all-inv-bit-bit (b (+ b (/ w 2))))))))

(local-defthm case-1-5
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (iff (all-1 a b (1+ i))
		           (and (all-1 a b i)
			        (= (bitn (ag i a) b) 1)))))))

(local-defthm case-1-6
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (iff (= (cnti z b (1+ i)) 1)
		           (all-1 a b (1+ i))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (case-1-3 case-1-4 case-1-5 all-inv-bit-bit
			(:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-1-7
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp j)
	   	           (<= j i)
	    	           (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (iff (all-0 a b j)
		           (all-0 a-next b j)))))
  :hints (("Goal" :induct (all-0 a b j))))

(local-defthm case-1-8
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (implies (= (cnti z b (1+ i)) 0)
		               (all-0 a b i)))))		           
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (all-inv-bit-bit
                        (:instance case-1-7 (j i))
                        (:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-1-9
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (iff (all-0 a b (1+ i))
		           (and (all-0 a b i)
			        (= (bitn (ag i a) b) 0)))))))

(local-defthm case-1-10
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (implies (= (cnti z b (1+ i)) 0)
		               (all-0 a b (1+ i))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (case-1-8 case-1-4 case-1-9 all-inv-bit-bit
			(:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-1-11
  (implies (and (bvecp z 64)1
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v-next) (loop-2-body i w a v)
             (declare (ignore a))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (equal (bitn v-next b)
		             (bitn v b)))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-v		  
                        (:instance all-inv-bit-bit (b (+ b (/ w 2))))))))

(local-defthm case-1-12
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore a))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (implies (> (cnti z b (1+ i)) 0)
		               (equal (bitn v b) 1)))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (case-1-11 all-inv-bit-bit
			(:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-1
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z (+ b w) i) 0))
		      (inv-bit z (1+ i) a v b))))
  :hints (("Goal" :in-theory (enable inv-bit)
                  :use (case-1-6 case-1-10 case-1-12))))

;;------------------------------

(local-defthm case-2-1
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp k)
	   	           (< k i)
	    	           (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (equal (bitn (ag k a-next) b)
		             (bitn (ag k a) (+ b w))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-a-k all-inv-bit-bit
			(:instance all-0-0 (j k))))))

(local-defthm case-2-2
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp j)
	   	           (<= j i)
	    	           (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (iff (all-1 a (+ b w) j)
		           (all-1 a-next b j)))))
  :hints (("Goal" :induct (nats j))))

(local-defthm case-2-3
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (iff (= (cnti z b (1+ i)) 1)
		           (all-1 a b i)))))		           
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use ((:instance case-2-2 (j i))
                        (:instance cnti-recurrence (i (1+ i)))
			(:instance all-inv-bit-bit (b (+ b (/ w 2))))))))

(local-defthm case-2-4
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v-next) (loop-2-body i w a v)
             (declare (ignore v-next))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (equal (bitn (ag i a-next) b)
		             (bitn v (+ b w))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-a-i all-inv-bit-bit))))

(local-defthm case-2-5
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (iff (all-1 a b (1+ i))
		           (and (all-1 a b i)
			        (= (bitn (ag i a) b) 1)))))))

(local-defthm case-2-6
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (iff (= (cnti z b (1+ i)) 1)
		           (all-1 a b (1+ i))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (case-2-3 case-2-4 case-2-5
		        (:instance all-inv-bit-bit (b (+ b (/ w 2))))
			(:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-2-7
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a-next v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp j)
	   	           (<= j i)
	    	           (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (iff (all-0 a (+ b w) j)
		           (all-0 a-next b j)))))
  :hints (("Goal" :induct (nats j))))

(local-defthm case-2-8
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (implies (= (cnti z b (1+ i)) 0)
		               (all-0 a b i)))))		           
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use ((:instance case-2-7 (j i))
                        (:instance cnti-recurrence (i (1+ i)))
			(:instance all-inv-bit-bit (b (+ b (/ w 2))))))))

(local-defthm case-2-9
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (iff (all-0 a b (1+ i))
		           (and (all-0 a b i)
			        (= (bitn (ag i a) b) 0)))))))

(local-defthm case-2-10
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore v))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (implies (= (cnti z b (1+ i)) 0)
		               (all-0 a b (1+ i))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (case-2-8 case-2-4 case-2-9
		        (:instance all-inv-bit-bit (b (+ b (/ w 2))))
			(:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-2-11
  (implies (and (bvecp z 64)1
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v-next) (loop-2-body i w a v)
             (declare (ignore a))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (equal (bitn v-next b)
		             (bitn v (+ b w))))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-v all-inv-bit-bit))))

(local-defthm case-2-12
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
             (declare (ignore a))
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (implies (> (cnti z b (1+ i)) 0)
		               (equal (bitn v b) 1)))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (case-2-11
		        (:instance all-inv-bit-bit (b (+ b (/ w 2))))
			(:instance cnti-recurrence (i (1+ i)))))))

(local-defthm case-2
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (implies (and (natp b)
		           (< b w)
			   (= (cnti z b i) 0))
		      (inv-bit z (1+ i) a v b))))
  :hints (("Goal" :in-theory (enable inv-bit)
                  :use (case-2-6 case-2-10 case-2-12))))

;;-------------------------------

(local-defthm case-3-1
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (implies (and (natp b)
		           (< b w)
			   (> (cnti z b i) 0)
			   (> (cnti z (+ b w) i) 0))
		      (and (> (cnti z b (1+ i)) 1)
		           (equal (bitn (ag i a) b) 0)
			   (equal (bitn v b) 1)))))
  :hints (("Goal" :in-theory (enable loop-2-body inv inv-bit)
                  :nonlinearp t
                  :use (bitn-a-i bitn-v all-inv-bit-bit
		        (:instance cnti-recurrence (i (1+ i)))
		        (:instance all-inv-bit-bit (b (+ b (/ w 2))))))))

(local-defthm case-3
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (implies (and (natp b)
		           (< b w)
			   (> (cnti z b i) 0)
			   (> (cnti z (+ b w) i) 0))
		      (inv-bit z (1+ i) a v b))))
  :hints (("Goal" :in-theory (enable inv-bit)
                  :use (case-3-1))))

;;--------------------------------

;; Combine the 3 cases and induct:

(local-defthm inv-bit-step
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (implies (and (natp b)
		           (< b w))
		      (inv-bit z (1+ i) a v b))))
  :hints (("Goal" :in-theory (enable inv-bit)
                  :use (case-1 case-2 case-3))))

(local-defthm all-inv-bit-step-1
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (implies (and (natp u)
		           (<= u w))
		      (all-inv-bit z (1+ i) a v u))))
  :hints (("Goal" :induct (nats u))
          ("Subgoal *1/2" :use ((:instance inv-bit-step (b (1- u)))))))

(local-defthm all-inv-bit-step
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (all-inv-bit z (1+ i) a v w)))
  :hints (("Goal" :use ((:instance all-inv-bit-step-1 (u w))))))

;; Combine the preceding lemma with natp-a-step:

(local-defthm loop-2-step
  (implies (and (bvecp z 64)
                (not (zp i))
		(< i 6)
		(inv z i w a v))
  	   (mv-let (w a v) (loop-2-body i w a v)
	     (inv z (1+ i) w a v)))
  :hints (("Goal" :in-theory (enable inv loop-2-body)
                  :use (all-inv-bit-step (:instance natp-a-step (u (1+ i)))))))

;;----------------------------------------------------------------------------------------

;; Use induction to combine loop-2-init and loop-2-step and establish the invariant:

(local-defthmd loop-2-induct
  (implies (and (bvecp z 64)
                (not (zp i))
		(<= i 6)
		(inv z i w a v))
	   (mv-let (w a v) (ispow2-loop-2-alt i w a v)
	     (inv z 6 w a v)))
  :hints (("Subgoal *1/4" :use (loop-2-step))
          ("Subgoal *1/3" :use (loop-2-step))))

(local-defthmd loop-2-inv
  (implies (bvecp z 64)
	   (mv-let (w a v) (ispow2-loop-2 0 64 () z)
	     (inv z 6 w a v)))
  :hints (("Goal" :in-theory (enable loop-2-rewrite)
                  :use (loop-2-init
                        (:instance loop-2-induct (i 1)
			                         (w (mv-nth 0 (mv-list 3 (loop-2-body 0 64 () z))))
			                         (a (mv-nth 1 (mv-list 3 (loop-2-body 0 64 () z))))
					         (v (mv-nth 2 (mv-list 3 (loop-2-body 0 64 () z)))))))))

;; Coming out of ispow2-loop-2, we only need Condition (3) (b) of the invariant:

(local-defthmd loop-2-lemma
  (implies (bvecp z 64)
           (iff (all-1 (mv-nth 1 (mv-list 3 (ispow2-loop-2 0 64 () z))) 0 6)
	        (= (cnti z 0 6) 1)))
  :hints (("Goal" :use (loop-2-inv) :in-theory (enable inv inv-bit))))

;; This leads trivially to the following characterizations of ispow2 for the positive
;; and negative cases:

(local-defthmd ispow2-cnt-1-pos
  (implies (bvecp x 64)
           (equal (ispow2 x 0)
	          (if (= (cnti x 0 6) 1)
		      1
		    0)))
  :hints (("Goal" :use ((:instance loop-2-lemma (z x)))
                  :in-theory (enable ispow2)
                  :expand ((:free (a b i) (all-1 a b i))
		           (:free (i a result) (ispow2-loop-0 i a result))))))

(local-defthmd ispow2-cnt-1-neg
  (implies (bvecp x 64)
           (equal (ispow2 x 1)
	          (if (= (cnti (bits (logxor (* 2 x) x) 63 0) 0 6) 1)
		      1
		    0)))
  :hints (("Goal" :use ((:instance loop-2-lemma (z (bits (logxor (* 2 x) x) 63 0))))
                  :in-theory (enable ispow2)
                  :expand ((:free (a b i) (all-1 a b i))
		           (:free (i a result) (ispow2-loop-0 i a result))))))

;; The main theorem for the positive case follows from ispow2-cnt-1-pos and cnt-1-pow2:

(local-defthmd ispow2-pos
  (implies (bvecp x 64)
           (equal (ispow2 x 0)
	          (if (= x (expt 2 (expo x)))
		      1
		    0)))
  :hints (("Goal" :use (ispow2-cnt-1-pos (:instance cnti-1-pow2 (z x))))))

;; The main theorem for the negative case follows from ispow2-cnt-1-neg, cnt-1-pow2,
;; and xor-pow2:

(local-defthmd ispow2-neg
  (implies (and (bvecp x 64) (not (= x 0)))
           (equal (ispow2 x 1)
	          (if (= (- (expt 2 64) x)
		         (expt 2 (expo (- (expt 2 64) x))))
		      1
		    0)))
  :hints (("Goal" :use (ispow2-cnt-1-neg xor-pow2-cor
                        (:instance cnti-1-pow2 (z (bits (logxor (* 2 x) x) 63
                                                        0)))))))

;;-------------------------------------------------------------------------------

;; An alternative proof using gl:

(defun bitrev (x n)
  (if (zp n)
      0
      (cat (bitrev (bits x (- n 2) 0) (1- n))
           (1- n)
           (bitn x (1- n))
	   1)))

(defun bitrevl (k n)
  (if (zp k)
      ()
     (cons (bitrev (1- k) n) (bitrevl (1- k) n))))

(defun bitrev-all (n) (bitrevl (expt 2 n) n))

;; The following runs in under a second.
;; (The 128-bit version runs in 47 seconds.)

(gl::def-gl-rule ispow2-gl-lemma
     :hyp
     (bvecp z 64)
     :concl
     (equal (ispow2-loop-0 0 (mv-nth 1 (mv-list 3 (ispow2-loop-2 0 64 () z))) 1)
            (if (= z (expt 2 (expo z)))
	        1
              0))
     :g-bindings
     `((z (:g-number ,(reverse (cons 64 (bitrev-all 6)))))))

(defthmd ispow2-pos-with-gl
  (implies (bvecp x 64)
           (equal (ispow2 x 0)
	          (if (= x (expt 2 (expo x)))
		      1
		    0)))
  :hints (("Goal" :in-theory (enable ispow2)
                  :use ((:instance ispow2-gl-lemma (z x))))))

(defthmd ispow2-neg-with-gl
  (implies (and (bvecp x 64) (not (= x 0)))
           (equal (ispow2 x 1)
	          (if (= (- (expt 2 64) x)
		         (expt 2 (expo (- (expt 2 64) x))))
		      1
		    0)))
  :hints (("Goal" :in-theory (enable ispow2)
                  :use (xor-pow2-cor (:instance ispow2-gl-lemma (z (bits (logxor (ash x 1) x) 63 0)))))))
