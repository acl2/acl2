(in-package "ACL2")

#|

This book is about LXOR, a nice version of LOGXOR.  LXOR takes an extra size parameter, N, and always returns
a bit vector of length N.

todo: ;add analogs of the thms in land.lisp past bitn-land

|#

;add macro alias

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund all-ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n)
      0 ;degenerate case
    (1- (expt 2 n))))

(local (include-book "all-ones"))
(local (include-book "merge"))
(local (include-book "bvecp"))
(local (include-book "logand"))
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "../arithmetic/top"))


(defund binary-lxor (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logxor (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro lxor (&rest x)
  (declare (xargs :guard (consp x)))
  (cond ((endp (cdddr x)) ;(lxor x y n) -- the base case
         `(binary-lxor ,@x))
        (t
         `(binary-lxor ,(car x)
                       (lxor ,@(cdr x))
                       ,(car (last x))))))


;Allows things like (in-theory (disable lxor)) to refer to binary-lxor.
(add-macro-alias lxor binary-lxor)


(defthm lxor-nonnegative-integer-type
  (and (integerp (lxor x y n))
       (<= 0 (lxor x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lxor) is no better than lxor-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lxor)))

;drop this if we plan to keep natp enabled?
(defthm lxor-natp
  (natp (lxor x y n)))

(defthm lxor-with-n-not-a-natp
  (implies (not (natp n))
           (equal (lxor x y n)
                  0))
  :hints (("Goal" :cases ((acl2-numberp n))
           :in-theory (enable lxor)))
  )

(defthmd lxor-bvecp-simple
  (bvecp (lxor x y n) n)
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable lxor))))

(defthm lxor-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lxor x y n) k))
  :hints (("Goal" :in-theory (disable lxor-bvecp-simple)
           :use lxor-bvecp-simple)))


;;
;; Rules to normalize lxor terms (recall that LXOR is a macro for BINARY-LXOR):
;;

;; allow sizes to differ on these?

(defthm lxor-associative
  (equal (lxor (lxor x y n) z n)
         (lxor x (lxor y z n) n))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable lxor bits-tail))))

(defthm lxor-commutative
  (equal (lxor y x n)
         (lxor x y n))
  :hints (("Goal" :in-theory (enable lxor))))

(defthm lxor-commutative-2
  (equal (lxor y (lxor x z n) n)
         (lxor x (lxor y z n) n))
  :hints (("Goal"  :cases ((natp n))
           :in-theory (enable lxor bits-tail))))

(defthm lxor-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (lxor x (lxor y z n) n)
                  (lxor (lxor x y n) z n))))

(defthm lxor-0
  (implies (case-split (bvecp y n))
           (equal (lxor 0 y n)
                  y))
  :hints (("Goal" :in-theory (enable lxor bits-tail))))

;nicer than the analogous rule for logand?
(defthm lxor-1
  (implies (case-split (bvecp y 1))
           (equal (lxor 1 y 1)
                  (lnot y 1)))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))

(defthm lxor-self
  (implies (case-split (bvecp x n))
           (equal (lxor x x n)
                  0))
  :hints (("Goal" :in-theory (enable lxor bits-tail))))


(defthmd bits-lxor-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lxor x y n) i j)
                  (lxor (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable lxor bits-logand))))


(defthmd bits-lxor-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lxor x y n) i j)
                  (lxor (bits x i j)
                        (bits y i j)
                        (+ n (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable lxor bits-logand))))

;notice the call to MIN in the conclusion
(defthm bits-lxor
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (lxor x y n) i j)
                  (lxor (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j)))))
  :hints (("Goal" :in-theory (enable bits-lxor-1 bits-lxor-2))))

(defthmd bitn-lxor-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor x y n) m)
                  (lxor (bitn x m)
                        (bitn y m)
                        1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '(BITS-N-N-REWRITE)))))
(defthmd bitn-lxor-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor x y n) m)
                  0))
  :hints (("Goal" :in-theory (enable BVECP-BITN-0))))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-lxor
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor x y n) m)
                  (if (< m n)
                      (lxor (bitn x m)
                            (bitn y m)
                            1)
                    0)))
  :hints (("Goal" :in-theory (enable bitn-lxor-1 bitn-lxor-2))))


(defthm lxor-ones
  (implies (case-split (bvecp x n))
           (equal (lxor (1- (expt 2 n)) x n)
                  (lnot x n)))
  :rule-classes ()
  :hints
  (("subgoal 1" :use logxor-ones)
   ("goal" :cases ((natp n))
    :in-theory (enable lxor bits-tail)
    )))

;lxor-with-all-ones will rewrite (lxor x n) [note there's only one value being ANDed], because (lxor x n)
;expands to (BINARY-LXOR X (ALL-ONES N) N) - now moot???
(defthm lxor-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (lxor (all-ones n) x n)
                  (lnot x n)))
  :hints
  (("goal" :use lxor-ones
    :in-theory (enable all-ones))))

(defthm lxor-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
                (case-split (bvecp x n)))
           (equal (lxor k x n)
                  (lnot x n)))
  :hints (("Goal" :use lxor-ones)))

(local (in-theory (disable mod-by-2-rewrite-to-even mod-mult-of-n mod-equal-0)))

(defthm lxor-def
    (implies (and (integerp x)
		  (integerp y)
		  (< 0 n)
                  (integerp n)
		  )
	     (equal (lxor x y n)
		    (+ (* 2 (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
		       (lxor (mod x 2) (mod y 2) 1))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (lxor bits-fl-by-2) ())
		  :use ((:instance logxor-def (i (bits x (1- n) 0)) (j (bits y (1- n) 0)))
			mod012
			(:instance mod012 (x y))))))

(defthm lxor-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (lxor x y n) 2)
		    (lxor (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use (lxor-def
			mod012
			(:instance mod012 (x y))
			(:instance quot-mod (m (lxor x y n)) (n 2))))))

(defthm lxor-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (lxor x y n) 2))
		    (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use (lxor-def
			mod012
			(:instance mod012 (x y))
			(:instance quot-mod (m (lxor x y n)) (n 2))))))

(in-theory (disable lxor-mod-2 lxor-fl-2))

(defthm bitn-lxor-0
    (implies (and (integerp x)
                  (integerp y)
		  (not (zp n))
                  )
	     (= (bitn (lxor x y n) 0)
		(bitn (+ x y) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-logxor-0 (a (bits x (1- n) 0)) (b (bits y (1- n) 0)))
			(:instance mod-mod-sum (n (expt 2 n)) (a x) (b y))
			(:instance mod-of-mod (a n) (b 1) (x (+ x y)))
			(:instance mod-of-mod (a n) (b 1) (x (+ (mod x (expt 2 n)) (mod y (expt 2 n))))))
		  :in-theory (enable lxor bitn-rec-0 bits-mod bitn-bits))))

(defthm lxor-x-y-0
  (equal (lxor x y 0) 0)
  :hints (("Goal" :in-theory (enable lxor))))


;N is a free variable
(defthm lxor-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (< n m)
		  (case-split (integerp m))
		  )
	     (equal (lxor x y m)
                    (lxor x y n)))
  :hints (("Goal" :in-theory (enable lxor))))


;move
(defthm lxor-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (lxor x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable lxor))))

;move
(defthm lxor-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (lxor x y n) (1- (expt 2 n)))))
