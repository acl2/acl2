(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system))

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
(include-book "rtl/rel11/support/definitions" :dir :system)

(local (encapsulate ()

(local (include-book "rtl/rel11/rel9-rtl-pkg/lib/log" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| mod-logand))


;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(in-theory (disable logand logior logxor))

(defthmd logand-def$
  (equal (logand x y)
         (if (or (zip x) (zip y))
             0
           (if (= x y)
               x
             (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
                (logand (mod x 2) (mod y 2))))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logand t t))))
  :hints (("Goal" :use ((:instance logand-def (i x) (j y))))))

(defthmd logior-def$
  (implies (and (integerp x) (integerp y))
           (equal (logior x y)
                  (if (or (zip x) (= x y))
                      y
                    (if (zip y)
                        x
                      (+ (* 2 (logior (fl (/ x 2)) (fl (/ y 2))))
                         (logior (mod x 2) (mod y 2)))))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logior t t))))
  :hints (("Goal" :use ((:instance logior-def (i x) (j y))))))

(defthmd logxor-def$
  (implies (and (integerp x) (integerp y))
           (equal (logxor x y)
                  (if (zip x)
                      y
                    (if (zip y)
                        x
                      (if (= x y)
                          0
                        (+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
                           (logxor (mod x 2) (mod y 2))))))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logxor t t))))
  :hints (("Goal" :use ((:instance logxor-def (i x) (j y))))))

(defthm logand-bnd$
    (implies (<= 0 x)
	     (and (<= 0 (logand x y))
                  (<= (logand x y) x)))
  :rule-classes :linear)

(defthm logand-bvecp
    (implies (and (natp n)
		  (bvecp x n)
		  (integerp y))
	     (bvecp (logand x y) n)))

(defthm logior-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n))
	     (bvecp (logior x y) n)))

(defthm logxor-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n))
	     (bvecp (logxor x y) n)))

(defthmd logand-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logand x y) (expt 2 n))
		    (logand (mod x (expt 2 n))
                            (mod y (expt 2 n)))))
  :hints (("Goal" :use acl2::mod-logand)))

(defthmd logior-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logior x y) (expt 2 n))
		    (logior (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd logxor-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logxor x y) (expt 2 n))
		    (logxor (mod x (expt 2 n))
                            (mod y (expt 2 n)))))
  :hints (("Goal" :use ((:instance bits-logxor (i (1- n)) (j 0)))
                  :in-theory (enable bits-mod))))

(defthmd fl-logand$
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logand x y)))
                  (logand (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y)))))
  :hints (("Goal" :use ((:instance fl-logand (k n) (n 0))))))

(defthmd fl-logior$
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logior x y)))
                  (logior (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y)))))
  :hints (("Goal" :use ((:instance fl-logior (k n) (n 0))))))

(defthmd fl-logxor$
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logxor x y)))
                  (logxor (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y)))))
  :hints (("Goal" :use ((:instance fl-logxor (k n) (n 0))))))

(local-defthmd logand-cat-1
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m))
                (natp k))
	   (equal (bitn (logand (cat x1 m y1 n) (cat x2 m y2 n)) k)
		  (bitn (cat (logand x1 x2) m (logand y1 y2) n) k)))
  :hints (("Goal" :in-theory (enable bitn-cat bitn-logand))))

(defthmd logand-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logand (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logand x1 x2) m (logand y1 y2) n)))
  :hints (("Goal" :in-theory (enable bitn-cat bitn-logand)
                  :use ((:instance bit-diff-diff (x (logand (cat x1 m y1 n) (cat x2 m y2 n)))
                                                 (y (cat (logand x1 x2) m (logand y1 y2) n)))))))

(defthmd logior-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logior (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logior x1 x2) m (logior y1 y2) n)))
  :hints (("Goal" :in-theory (enable bitn-cat bitn-logior)
                  :use ((:instance bit-diff-diff (x (logior (cat x1 m y1 n) (cat x2 m y2 n)))
                                                 (y (cat (logior x1 x2) m (logior y1 y2) n)))))))

(defthmd logxor-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logxor (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logxor x1 x2) m (logxor y1 y2) n)))
  :hints (("Goal" :in-theory (enable bitn-cat bitn-logxor)
                  :use ((:instance bit-diff-diff (x (logxor (cat x1 m y1 n) (cat x2 m y2 n)))
                                                 (y (cat (logxor x1 x2) m (logxor y1 y2) n)))))))

(defthmd logand-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logand (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logand x y)))))

(defthmd logior-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logior (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logior x y)))))

(defthmd logxor-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logxor (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logxor x y)))))

(defthm logand-expt$
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal" :use logand-expt)))

(local-defthm le-1
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (mod (logior (* (expt 2 n) x) y) (expt 2 n))
		(mod (+ (* (expt 2 n) (logior x (fl (/ y (expt 2 n)))))
                        (mod y (expt 2 n)))
                     (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable logior-mod))))

(defthm integerp-fl
  (implies (integerp x)
           (equal (fl x) x)))

(local-defthm le-2
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (fl (/ (logior (* (expt 2 n) x) y) (expt 2 n)))
		(fl (/ (+ (* (expt 2 n) (logior x (fl (/ y (expt 2 n)))))
                          (mod y (expt 2 n)))
                       (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fl-logior$))))

(defthm logior-expt$
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) (logior x (fl (/ y (expt 2 n)))))
                   (mod y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (le-1 le-2
                        (:instance mod-def (x (logior (* (expt 2 n) x) y)) (y (expt 2 n)))
                        (:instance mod-def (x (+ (* (expt 2 n) (logior x (fl (/ y (expt 2 n))))) (mod y (expt 2 n)))) (y (expt 2 n)))))))

(local-defthm le-3
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (mod (logxor (* (expt 2 n) x) y) (expt 2 n))
		(mod (+ (* (expt 2 n) (logxor x (fl (/ y (expt 2 n)))))
                        (mod y (expt 2 n)))
                     (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable logxor-mod))))

(local-defthm le-4
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (fl (/ (logxor (* (expt 2 n) x) y) (expt 2 n)))
		(fl (/ (+ (* (expt 2 n) (logxor x (fl (/ y (expt 2 n)))))
                          (mod y (expt 2 n)))
                       (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fl-logxor$))))

(defthm logxor-expt$
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (logxor (* (expt 2 n) x) y)
		(+ (* (expt 2 n) (logxor x (fl (/ y (expt 2 n)))))
                   (mod y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (le-3 le-4
                        (:instance mod-def (x (logxor (* (expt 2 n) x) y)) (y (expt 2 n)))
                        (:instance mod-def (x (+ (* (expt 2 n) (logxor x (fl (/ y (expt 2 n))))) (mod y (expt 2 n)))) (y (expt 2 n)))))))

(defthm logior-expt-cor$
    (implies (and (natp n)
		  (integerp x)
		  (bvecp y n))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal" :use logior-expt)))

(local-defthm logior-2**n-1
  (implies (and (natp n)
                (integerp x))
           (= (mod (logior (expt 2 n) x) (expt 2 (1+ n)))
              (if (= (bitn x n) 1)
                  (mod x (expt 2 (1+ n)))
                (+ (mod x (expt 2 (1+ n))) (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (bitn-0-1
                        (:instance bitn-plus-bits (m 0))
                        (:instance logior-cat (x1 (bitn x n)) (y1 (bits x (1- n) 0)) (x2 1) (y2 0) (m 1)))
                  :in-theory (enable logior-mod bits binary-cat))))

(local-defthm logior-2**n-2
  (implies (and (natp n)
                (integerp x))
           (= (fl (/ (logior (expt 2 n) x) (expt 2 (1+ n))))
              (fl (/ x (expt 2 (1+ n))))))
  :rule-classes ()
  :hints (("Goal" :use (:instance fl-logior$ (x (expt 2 n)) (y x) (n (1+ n))))))

(defthmd logior-2**n
  (implies (and (natp n)
                (integerp x))
           (equal (logior (expt 2 n) x)
                  (if (= (bitn x n) 1)
                      x
                    (+ x (expt 2 n)))))
  :hints (("Goal" :use (logior-2**n-1 logior-2**n-2
                        (:instance mod-def (y (expt 2 (1+ n))))
                        (:instance mod-def (x (logior (expt 2 n) x)) (y (expt 2 (1+ n))))))))

(defthmd logand-bits
    (implies (and (integerp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (equal (logand x (- (expt 2 n) (expt 2 k)))
		    (* (expt 2 k) (bits x (1- n) k))))
  :hints (("Goal" :use logand-expt-3)))

(local-defthm lb-1
    (implies (natp n)
	     (equal (+ (- (EXPT 2 N)) (EXPT 2 (+ 1 N)))
                    (expt 2 n))))

(defthmd logand-bit
    (implies (and (integerp x)
		  (natp n))
	     (equal (logand x (expt 2 n))
		    (* (expt 2 n) (bitn x n))))
  :hints (("Goal" :use ((:instance logand-bits (n (1+ n)) (k n))))))

(defthmd bits-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i)
		  (integerp j))
	     (equal (bits (logand x y) i j)
		    (logand (bits x i j) (bits y i j))))
  :hints (("Goal" :cases ((natp i)))
          ("Subgoal 1" :cases ((natp j)) :in-theory (enable bits fl-logand$ logand-shift logand-mod))))

(defthmd bits-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
	     (equal (bits (logior x y) i j)
                    (logior (bits x i j) (bits y i j)))))

(defthmd bits-logxor$
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
           (equal (bits (logxor x y) i j)
                  (logxor (bits x i j) (bits y i j))))
  :hints (("Goal" :in-theory (enable bits-logxor))))

(defthmd bitn-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn (logand x y) n)
		    (logand (bitn x n) (bitn y n)))))

(defthmd bitn-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn (logior x y) n)
		    (logior (bitn x n) (bitn y n)))))

(defthmd bitn-logxor
    (implies (and (case-split (integerp x))
		  (case-split (integerp y))
		  (case-split (integerp n)))
	     (equal (bitn (logxor x y) n)
		    (logxor (bitn x n) (bitn y n)))))


;;;**********************************************************************
;;;                               LOGNOT
;;;**********************************************************************

(in-theory (disable lognot))

(defthmd lognot-def
    (implies (integerp x)
	     (equal (lognot x)
		    (1- (- x)))))

(defthmd lognot-shift
  (implies (and (integerp x)
                (natp k))
           (equal (lognot (* (expt 2 k) x))
		  (+ (* (expt 2 k) (lognot x))
		     (1- (expt 2 k))))))

(defthmd lognot-fl
  (implies (and (integerp x)
                (not (zp n)))
           (equal (lognot (fl (/ x n)))
                  (fl (/ (lognot x) n)))))

(defthmd mod-lognot
  (implies (and (integerp x)
                (natp n))
           (equal (mod (lognot x) (expt 2 n))
                  (1- (- (expt 2 n) (mod x (expt 2 n))))))
  :hints (("Goal" :in-theory (enable lognot-def)
                  :use ((:instance mod-mult (m (lognot x)) (a (1+ (fl (/ x (expt 2 n))))) (n (expt 2 n)))
                        (:instance mod-def (y (expt 2 n)))))))

(defthmd bits-lognot
    (implies (and (natp i)
		  (natp j)
		  (<= j i)
		  (integerp x))
	     (equal (bits (lognot x) i j)
		    (- (1- (expt 2 (- (1+ i) j))) (bits x i j)))))

(defthm bitn-lognot$
  (implies (and (integerp x)
                (natp n))
           (not (equal (bitn (lognot x) n)
                (bitn x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn bits-lognot))))

(defthmd bits-lognot-bits
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits x i j)) k l)
                  (bits (lognot x) (+ k j) (+ l j)))))

(defthmd bits-lognot-bits-lognot
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits (lognot x) i j)) k l)
                  (bits x (+ k j) (+ l j)))))

(defthmd logand-bits-lognot$
  (implies (and (integerp x)
                (integerp n)
                (bvecp y n))
           (equal (logand y (bits (lognot x) (1- n) 0))
                  (logand y (lognot (bits x (1- n) 0)))))
  :hints (("Goal" :use ((:instance logand-bits-lognot (n (1- n)))))))


;;;**********************************************************************
;;;                         Algebraic Properties
;;;**********************************************************************

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logior-x-0
    (implies (integerp x)
	     (equal (logior x 0) x)))

(defthm logior-0-y
    (implies (integerp y)
	     (equal (logior 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logand-self$
  (implies (case-split (integerp i))
           (equal (logand i i) i))
  :hints (("Goal" :use logand-self)))

(defthm logior-self$
    (implies (case-split (integerp i))
	     (equal (logior i i) i))
  :hints (("Goal" :use logior-self)))

(defthm logxor-self$
  (equal (logxor i i) 0)
  :hints (("Goal" :use logxor-self)))

(defthm lognot-lognot$
    (implies (case-split (integerp i))
	     (equal (lognot (lognot i))
		    i))
  :hints (("Goal" :use lognot-lognot)))

(defthmd logior-not-0$
  (implies (and (integerp x)
                (integerp y))
           (iff (equal (logior x y) 0)
                (and (= x 0) (= y 0))))
  :hints (("Goal" :use (logior-not-0))))

(defthmd logxor-not-0
  (implies (and (integerp x)
                (integerp y))
           (iff (equal (logxor x y) 0)
                (= x y)))
  :hints (("Goal" :use (bit-diff-diff
                        (:instance bitn-logxor (n (bit-diff x y)))
                        (:instance bitn-0-1 (n (bit-diff x y)))
                        (:instance bitn-0-1 (x y) (n (bit-diff x y)))))))

(defthm logand-x-1
    (implies (bvecp x 1)
	     (equal (logand x 1) x)))

(defthm logand-1-x
    (implies (bvecp x 1)
	     (equal (logand 1 x) x)))

(defthm logior-1-x
  (implies (bvecp x 1)
           (equal (logior 1 x) 1)))

(defthm logior-x-1
  (implies (bvecp x 1)
           (equal (logior x 1) 1)))

(defthm logand-x-m1
    (implies (integerp x)
	     (equal (logand x -1) x)))

(defthm logand-m1-y
    (implies (integerp y)
	     (equal (logand -1 y) y)))

(defthm logior-x-m1
    (implies (integerp x)
	     (equal (logior x -1) -1)))

(defthm logior-m1-y
    (implies (integerp y)
	     (equal (logior -1 y) -1)))

(defthm logxor-x-m1
    (implies (integerp x)
	     (equal (logxor x -1)
		    (lognot x))))

(defthm logxor-m1-x
    (implies (integerp x)
	     (equal (logxor -1 x)
		    (lognot x))))

(defthm logand-commutative$
    (equal (logand j i) (logand i j))
  :hints (("Goal" :use logand-commutative)))

(defthm logior-commutative$
    (equal (logior j i) (logior i j))
  :hints (("Goal" :use logior-commutative)))

(defthm logxor-commutative$
    (equal (logxor j i) (logxor i j))
  :hints (("Goal" :use logxor-commutative)))

(defthm logand-commutative-2$
  (equal (logand j i k)
	 (logand i j k))
  :hints (("Goal" :use logand-commutative-2)))

(defthm logior-commutative-2$
  (equal (logior j i k)
	 (logior i j k))
  :hints (("Goal" :use logior-commutative-2)))

(defthm logxor-commutative-2$
  (equal (logxor j i k)
	 (logxor i j k))
  :hints (("Goal" :use logxor-commutative-2)))

(defthm logand-associative$
    (equal (logand (logand i j) k)
           (logand i (logand j k)))
  :hints (("Goal" :use logand-associative)))

(defthm logior-associative$
    (equal (logior (logior i j) k)
	   (logior i (logior j k)))
  :hints (("Goal" :use logior-associative)))

(defthm logxor-associative$
    (equal (logxor (logxor i j) k)
	   (logxor i (logxor j k)))
  :hints (("Goal" :use logxor-associative)))

(defthmd logior-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logior x (logand y z))
                  (logand (logior x y) (logior x z)))))

(defthmd logior-logand-1
  (implies (and (integerp x)
                (integerp y))
           (equal (logior x (logand x y))
                  x))
  :hints (("Goal"
           :in-theory (enable bitn-logior bitn-logand)
           :use ((:instance bit-diff-diff
                            (y (logior x (logand x y))))
                 (:instance bitn-0-1
                            (n (bit-diff x (logior x (logand x y)))))
                 (:instance bitn-0-1
                            (x (logior x (logand x y)))
                            (n (bit-diff x (logior x (logand x y)))))))))

(defthmd logand-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand x (logior y z))
	   (logior (logand x y) (logand x z)))))

(defthmd logior-logand-2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand (logior y z) x)
	   (logior (logand y x) (logand z x)))))

(defthmd log3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logior (logand x y) (logior (logand x z) (logand y z)))
	   (logior (logand x y) (logand (logxor x y) z)))))

(defthmd logxor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand y (lognot x)))))
  :hints (("Goal" :in-theory (enable logxor-rewrite-2))))

(defthmd lognot-logxor$
    (and (equal (logxor (lognot i) j)
                (lognot (logxor i j)))
         (equal (logxor j (lognot i))
                (lognot (logxor i j))))
  :hints (("Goal" :use lognot-logxor)))

))

;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(in-theory (disable logand logior logxor))

(defthmd logand-def
  (equal (logand x y)
         (if (or (zip x) (zip y))
             0
           (if (= x y)
               x
             (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
                (logand (mod x 2) (mod y 2))))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logand t t))))
  :hints (("Goal" :use logand-def$)))

(defthmd logior-def
  (implies (and (integerp x) (integerp y))
           (equal (logior x y)
                  (if (or (zip x) (= x y))
                      y
                    (if (zip y)
                        x
                      (+ (* 2 (logior (fl (/ x 2)) (fl (/ y 2))))
                         (logior (mod x 2) (mod y 2)))))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logior t t))))
  :hints (("Goal" :use logior-def$)))

(defthmd logxor-def
  (implies (and (integerp x) (integerp y))
           (equal (logxor x y)
                  (if (zip x)
                      y
                    (if (zip y)
                        x
                      (if (= x y)
                          0
                        (+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
                           (logxor (mod x 2) (mod y 2))))))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logxor t t))))
  :hints (("Goal" :use logxor-def$)))

(defthm logand-bnd
    (implies (<= 0 x)
	     (and (<= 0 (logand x y))
                  (<= (logand x y) x)))
  :rule-classes :linear
  :hints (("Goal" :use logand-bnd$)))

(defthm logand-bvecp
    (implies (and (natp n)
		  (bvecp x n)
		  (integerp y))
	     (bvecp (logand x y) n)))

(defthm logior-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n))
	     (bvecp (logior x y) n)))

(defthm logxor-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n))
	     (bvecp (logxor x y) n)))

(defthmd logand-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logand x y) (expt 2 n))
		    (logand (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd logior-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logior x y) (expt 2 n))
		    (logior (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd logxor-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logxor x y) (expt 2 n))
		    (logxor (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd fl-logand
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logand x y)))
                  (logand (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y)))))
  :hints (("Goal" :use fl-logand$)))

(defthmd fl-logior
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logior x y)))
                  (logior (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y)))))
  :hints (("Goal" :use fl-logior$)))

(defthmd fl-logxor
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logxor x y)))
                  (logxor (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y)))))
  :hints (("Goal" :use fl-logxor$)))

(defthmd logand-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logand (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logand x1 x2) m (logand y1 y2) n))))

(defthmd logior-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logior (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logior x1 x2) m (logior y1 y2) n))))

(defthmd logxor-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logxor (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logxor x1 x2) m (logxor y1 y2) n))))

(defthmd logand-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logand (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logand x y)))))

(defthmd logior-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logior (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logior x y)))))

(defthmd logxor-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logxor (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logxor x y)))))

(defthmd logand-expt
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (equal (logand (* (expt 2 n) x) y)
	  	    (* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :hints (("Goal" :use logand-expt$)))

(defthmd logior-expt
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (equal (logior (* (expt 2 n) x) y)
	   	    (+ (* (expt 2 n) (logior x (fl (/ y (expt 2 n)))))
                       (mod y (expt 2 n)))))
  :hints (("Goal" :use logior-expt$)))

(defthmd logxor-expt
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (equal (logxor (* (expt 2 n) x) y)
		(+ (* (expt 2 n) (logxor x (fl (/ y (expt 2 n)))))
                   (mod y (expt 2 n)))))
  :hints (("Goal" :use logxor-expt$)))

(defthmd logior-expt-cor
    (implies (and (natp n)
		  (integerp x)
		  (bvecp y n))
	     (equal (logior (* (expt 2 n) x) y)
	   	    (+ (* (expt 2 n) x) y)))
  :hints (("Goal" :use logior-expt-cor$)))

(defthmd logior-2**n
  (implies (and (natp n)
                (integerp x))
           (equal (logior (expt 2 n) x)
                  (if (= (bitn x n) 1)
                      x
                    (+ x (expt 2 n))))))

(defthmd logand-bits
    (implies (and (integerp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (equal (logand x (- (expt 2 n) (expt 2 k)))
		    (* (expt 2 k) (bits x (1- n) k)))))

(defthmd logand-bit
    (implies (and (integerp x)
		  (natp n))
	     (equal (logand x (expt 2 n))
		    (* (expt 2 n) (bitn x n)))))

(defthmd bits-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i)
		  (integerp j))
	     (equal (bits (logand x y) i j)
		    (logand (bits x i j) (bits y i j)))))

(defthmd bits-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
	     (equal (bits (logior x y) i j)
                    (logior (bits x i j) (bits y i j)))))

(defthmd bits-logxor
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
           (equal (bits (logxor x y) i j)
                  (logxor (bits x i j) (bits y i j))))
  :hints (("Goal" :use bits-logxor$)))

(defthmd bitn-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn (logand x y) n)
		    (logand (bitn x n) (bitn y n)))))

(defthmd bitn-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn (logior x y) n)
		    (logior (bitn x n) (bitn y n)))))

(defthmd bitn-logxor
    (implies (and (case-split (integerp x))
		  (case-split (integerp y))
		  (case-split (integerp n)))
	     (equal (bitn (logxor x y) n)
		    (logxor (bitn x n) (bitn y n)))))



(defun log-induct (x y)
  (declare (xargs :measure (abs (* (ifix x) (ifix y)))
                  :hints (("Subgoal 1" :nonlinearp t
		                       :use ((:instance fl-half-int (n x))
                                             (:instance fl-half-int (n y)))))))
  (if (or (not (integerp x)) (not (integerp y)) (= x 0) (= y 0) (= x y))
      (+ x y)
    (log-induct (fl (/ x 2)) (fl (/ y 2)))))
    
(defthmd logand-plus-logxor
  (implies (and (integerp x)
                (integerp y))
	   (equal (+ (logand x y) (logxor x y))
	          (logior x y)))
  :hints (("Goal" :induct (log-induct x y))
          ("Subgoal *1/2" :use (logand-def logior-def logxor-def
			        (:instance mod012 (m x))
			        (:instance mod012 (m y))))))



;;;**********************************************************************
;;;                               LOGNOT
;;;**********************************************************************

(in-theory (disable lognot))

(defthmd lognot-def
    (implies (integerp x)
	     (equal (lognot x)
		    (1- (- x)))))

(defthmd lognot-shift
  (implies (and (integerp x)
                (natp k))
           (equal (lognot (* (expt 2 k) x))
		  (+ (* (expt 2 k) (lognot x))
		     (1- (expt 2 k))))))

(defthmd lognot-fl
  (implies (and (integerp x)
                (not (zp n)))
           (equal (lognot (fl (/ x n)))
                  (fl (/ (lognot x) n)))))

(defthmd mod-lognot
  (implies (and (integerp x)
                (natp n))
           (equal (mod (lognot x) (expt 2 n))
                  (1- (- (expt 2 n) (mod x (expt 2 n)))))))

(defthmd bits-lognot
    (implies (and (natp i)
		  (natp j)
		  (<= j i)
		  (integerp x))
	     (equal (bits (lognot x) i j)
		    (- (1- (expt 2 (- (1+ i) j))) (bits x i j)))))

(defthm bitn-lognot
  (implies (and (integerp x)
                (natp n))
           (not (equal (bitn (lognot x) n)
                       (bitn x n))))
  :rule-classes ()
  :hints (("Goal" :use bitn-lognot$)))

(defthmd bits-lognot-bits
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits x i j)) k l)
                  (bits (lognot x) (+ k j) (+ l j)))))

(defthmd bits-lognot-bits-lognot
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits (lognot x) i j)) k l)
                  (bits x (+ k j) (+ l j)))))

(defthmd logand-bits-lognot
  (implies (and (integerp x)
                (integerp n)
                (bvecp y n))
           (equal (logand y (bits (lognot x) (1- n) 0))
                  (logand y (lognot (bits x (1- n) 0)))))
  :hints (("Goal" :use logand-bits-lognot$)))


;;;**********************************************************************
;;;                         Algebraic Properties
;;;**********************************************************************

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logior-x-0
    (implies (integerp x)
	     (equal (logior x 0) x)))

(defthm logior-0-y
    (implies (integerp y)
	     (equal (logior 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logand-self
  (implies (case-split (integerp x))
           (equal (logand x x) x))
  :hints (("Goal" :use (:instance logand-self$ (i x)))))

(defthm logior-self
    (implies (case-split (integerp x))
	     (equal (logior x x) x))
  :hints (("Goal" :use (:instance logior-self$ (i x)))))

(defthm logxor-self
  (equal (logxor x x) 0)
  :hints (("Goal" :use logxor-self$)))

; Matt K. edit: changed variable x to i to match ihs/logops-lemmas.lisp.
(defthm lognot-lognot
    (implies (case-split (integerp i))
	     (equal (lognot (lognot i))
		    i))
  :hints (("Goal" :use (:instance lognot-lognot$))))

(defthmd logior-not-0
  (implies (and (integerp x)
                (integerp y))
           (iff (equal (logior x y) 0)
                (and (= x 0) (= y 0))))
  :hints (("Goal" :use logior-not-0$)))

(defthmd logxor-not-0
  (implies (and (integerp x)
                (integerp y))
           (iff (equal (logxor x y) 0)
                (= x y))))

(defthm logand-x-1
    (implies (bvecp x 1)
	     (equal (logand x 1) x)))

(defthm logand-1-x
    (implies (bvecp x 1)
	     (equal (logand 1 x) x)))

(defthm logior-1-x
  (implies (bvecp x 1)
           (equal (logior 1 x) 1)))

(defthm logior-x-1
  (implies (bvecp x 1)
           (equal (logior x 1) 1)))

(defthm logand-x-m1
    (implies (integerp x)
	     (equal (logand x -1) x)))

(defthm logand-m1-y
    (implies (integerp y)
	     (equal (logand -1 y) y)))

(defthm logior-x-m1
    (implies (integerp x)
	     (equal (logior x -1) -1)))

(defthm logior-m1-y
    (implies (integerp y)
	     (equal (logior -1 y) -1)))

(defthm logxor-x-m1
    (implies (integerp x)
	     (equal (logxor x -1)
		    (lognot x))))

(defthm logxor-m1-x
    (implies (integerp x)
	     (equal (logxor -1 x)
		    (lognot x))))

(defthm logand-commutative
    (equal (logand y x) (logand x y))
  :hints (("Goal" :use (:instance logand-commutative$ (i x) (j y)))))

(defthm logior-commutative
    (equal (logior y x) (logior x y))
  :hints (("Goal" :use (:instance logior-commutative$ (i x) (j y)))))

(defthm logxor-commutative
    (equal (logxor y x) (logxor x y))
  :hints (("Goal" :use (:instance logxor-commutative$ (i x) (j y)))))

(defthm logand-commutative-2
  (equal (logand y x z)
	 (logand x y z))
  :hints (("Goal" :use (:instance logand-commutative-2$ (i x) (j y) (k z)))))

(defthm logior-commutative-2
  (equal (logior y x z)
	 (logior x y z))
  :hints (("Goal" :use (:instance logior-commutative-2$ (i x) (j y) (k z)))))

(defthm logxor-commutative-2
  (equal (logxor y x z)
	 (logxor x y z))
  :hints (("Goal" :use (:instance logxor-commutative-2$ (i x) (j y) (k z)))))

(defthm logand-associative
    (equal (logand (logand x y) z)
           (logand x (logand y z)))
  :hints (("Goal" :use (:instance logand-associative$ (i x) (j y) (k z)))))

(defthm logior-associative
    (equal (logior (logior x y) z)
	   (logior x (logior y z)))
  :hints (("Goal" :use (:instance logior-associative$ (i x) (j y) (k z)))))

(defthm logxor-associative
    (equal (logxor (logxor x y) z)
	   (logxor x (logxor y z)))
  :hints (("Goal" :use (:instance logxor-associative$ (i x) (j y) (k z)))))

(defthmd logior-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logior x (logand y z))
                  (logand (logior x y) (logior x z)))))

(defthmd logior-logand-1
  (implies (and (integerp x)
                (integerp y))
           (equal (logior x (logand x y))
                  x))
  :hints (("Goal"
           :in-theory (enable bitn-logior bitn-logand)
           :use ((:instance bit-diff-diff
                            (y (logior x (logand x y))))
                 (:instance bitn-0-1
                            (n (bit-diff x (logior x (logand x y)))))
                 (:instance bitn-0-1
                            (x (logior x (logand x y)))
                            (n (bit-diff x (logior x (logand x y)))))))))

(defthmd logand-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand x (logior y z))
	   (logior (logand x y) (logand x z)))))

(defthmd logior-logand-2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand (logior y z) x)
	   (logior (logand y x) (logand z x)))))

(defthmd log3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logior (logand x y) (logior (logand x z) (logand y z)))
	   (logior (logand x y) (logand (logxor x y) z)))))

(defthmd logxor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand y (lognot x))))))

(defthmd lognot-logxor
    (and (equal (logxor (lognot x) y)
                (lognot (logxor x y)))
         (equal (logxor y (lognot x))
                (lognot (logxor x y))))
  :hints (("Goal" :use (:instance lognot-logxor$ (i x) (j y)))))
