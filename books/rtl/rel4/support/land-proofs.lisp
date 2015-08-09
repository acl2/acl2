(in-package "ACL2")

#|

This book is about LAND, a nice version of LOGAND.  LAND takes an extra size parameter, N, and always returns
a bit vector of length N.

Todo:
add versions of logand-expt-2 and logand-expt-4
prove (elsewhere) lemmas mixing land with other functions
what should land of non-ints be?

think about removing bits from defn of land? why???
|#

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

(local (include-book "bvecp"))
(local (include-book "all-ones"))
(local (include-book "log"))
(local (include-book "merge")) ;drop?
(local (include-book "bvecp"))
(local (include-book "logand"))
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "../arithmetic/top"))

;We expect n to be a positive integer, and x and y to be bit vectors of length n.
(defund binary-land (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logand (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro land (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(land x y n) -- the base case
         `(binary-land ,@x))
        (t
         `(binary-land ,(car x)
                       (land ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable land)) to refer to binary-land.
(add-macro-alias land binary-land)

(defthm land-nonnegative-integer-type
  (and (integerp (land x y n))
       (<= 0 (land x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription land) is no better than land-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-land)))

;drop this if we plan to keep natp enabled?
(defthm land-natp
  (natp (land x y n)))

(defthm land-with-n-not-a-natp
  (implies (not (natp n))
           (equal (land x y n)
                  0))
  :hints (("Goal" :cases ((acl2-numberp n))
           :in-theory (enable land)))
  )

(defthmd land-bvecp-simple
  (bvecp (land x y n) n)
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable land))))

(defthm land-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (land x y n) k))
  :hints (("Goal" :in-theory (disable land-bvecp-simple)
           :use land-bvecp-simple)))


;;
;; Rules to normalize land terms (recall that LAND is a macro for BINARY-LAND):
;;

;; allow sizes to differ on these?

(defthm land-associative
  (equal (land (land x y n) z n)
         (land x (land y z n) n))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable land bits-tail))))

#|
;move
(defthm logand-tighten-helper
  (implies (bvecp x m)
           (equal (logand x y)
                  (logand (bits x (1- m) 0) y))))

(defthm land-tighten-1
  (implies (and (< m n)
                (integerp m)
                (integerp n))
           (equal (land (land x y m) z n)
                  (land (land x y m) z m)))
  :hints (("Goal" :in-theory (enable bits-tail)
           :expand ((BINARY-LAND Z (BINARY-LAND X Y M) N)))))


(defthm land-associative-gen
  (implies (and (integerp m)
                (integerp n)
                (<= 0 m)
                (<= 0 n)
                (<= m n)
;                (bvecp x m)
;                (bvecp z n)
                )
  (equal (land (land x y m) z n)
         (land x (land y z m) m)))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable land bits-tail))))
  |#

(defthm land-commutative
  (equal (land y x n)
         (land x y n))
  :hints (("Goal" :in-theory (enable land))))

;gen (must the n's match)?
(defthm land-commutative-2
  (equal (land y (land x z n) n)
         (land x (land y z n) n))
  :hints (("Goal"  :cases ((natp n))
           :in-theory (enable land bits-tail))))

(defthm land-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (land x (land y z n) n)
                  (land (land x y n) z n))))


(defthm land-0
  (equal (land 0 y n)
         0)
  :hints (("Goal" :in-theory (enable land))))

;nicer than the analogous rule for logand?
;would like to let the 1 be any n?
(defthm land-1
  (equal (land 1 y 1)
         (bitn y 0))
  :hints (("Goal" :in-theory (enable land bitn))))

(defthm land-self
  (equal (land x x n)
         (bits x (1- n) 0))
  :hints (("Goal" :in-theory (enable land bits-tail))))

(defthmd bits-land-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable land bits-logand))))


(defthmd bits-land-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ n (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable land bits-logand))))

;notice the call to MIN in the conclusion
(defthm bits-land
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j)))))
  :hints (("Goal" :in-theory (enable bits-land-1 bits-land-2))))

(defthmd bitn-land-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  (land (bitn x m)
                        (bitn y m)
                        1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '(BITS-N-N-REWRITE)))))
(defthmd bitn-land-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  0))
  :hints (("Goal" :in-theory (enable bvecp-bitn-0))))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-land
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  (if (< m n)
                      (land (bitn x m)
                            (bitn y m)
                            1)
                    0)))
  :hints (("Goal" :in-theory (enable bitn-land-1 bitn-land-2))))

;BOZO see land-equal-0
;drop bvecp hyps and out bitn in conclusion?
(defthm land-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (land x y 1))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))

(defthm land-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (land x y 1))
                  (and (equal x 1)
                       (equal y 1))))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))



;in general, rewrite (bvecp k n) where k is a constant to a fact about n

;BOZO allow the n's to differ?
(defthm land-ones
  (equal (land (1- (expt 2 n)) x n)
         (bits x (1- n) 0))
  :rule-classes ()
  :hints (("goal" :cases ((natp n))
           :in-theory (enable land bits-tail logand-ones bvecp)
           )))

#| old:
(defthm land-ones
  (implies (case-split (bvecp x n))
           (equal (land (1- (expt 2 n)) x n)
                  x))
  :rule-classes ()
  :hints (("goal" :cases ((natp n))
           :in-theory (enable land bits-tail logand-ones bvecp)
           )))
|#

;land-with-all-ones will rewrite (land x n) [note there's only one value being ANDed], because (land x n)
;expands to (BINARY-LAND X (ALL-ONES N) N) - now moot???
(defthm land-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (land (all-ones n) x n)
                  x))
  :hints (("goal" :use land-ones
           :in-theory (enable all-ones))))

#| old
(defthm land-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
                (case-split (bvecp x n)))
           (equal (land k x n)
                  x))
  :hints (("Goal" :use land-ones)))
|#

(defthmd land-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (equal k (1- (expt 2 n))) ;this computes on constants...
                )
           (equal (land k x n)
                  (bits x (1- n) 0)))
  :hints (("Goal" :use (:instance land-ones))))


(local (in-theory (disable mod-by-2-rewrite-to-even mod-mult-of-n mod-equal-0 )))

(defthm land-def
  (implies (and (integerp x)
                (integerp y)
                (> n 0)
                (integerp n) ;(natp n)
                )
           (equal (land x y n)
                  (+ (* 2 (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land (mod x 2) (mod y 2) 1))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (land bits-fl-by-2) ())
           :use ((:instance logand-rewrite (x (bits x (1- n) 0)) (y (bits y (1- n) 0)))
                 mod012
                 (:instance mod012 (x y))))))

(defthm land-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (land x y n) 2)
		    (land (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use (land-def
			mod012
			(:instance mod012 (x y))
			(:instance quot-mod (m (land x y n)) (n 2))))))

(defthm land-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (land x y n) 2))
		    (land (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use (land-def
			mod012
			(:instance mod012 (x y))
			(:instance quot-mod (m (land x y n)) (n 2))))))

(in-theory (disable land-mod-2 land-fl-2))

;BOZO rename to land-with-n-0
;what if n is negative? or not an integer?
(defthm land-x-y-0
    (equal (land x y 0) 0)
  :hints (("Goal" :in-theory (enable land))))

;actually, maybe only either x or y must be a bvecp of length n
;n is a free var
(defthm land-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land x y m)
                    (land x y n)))
  :hints (("Goal" :in-theory (enable land))))

;BOZO move to logand?
(local
 (defthm logand-of-single-bits-equal-0
   (implies (and (bvecp i 1)
                 (bvecp j 1))
            (equal (equal 0 (logand i j))
                   (or (equal i 0)
                       (equal j 0))))
   :hints (("Goal" :in-theory (enable bvecp-1-rewrite)))))

;deceptive name; this only works for single bits!
(defthm land-equal-0
  (implies (and (bvecp i 1)
                (bvecp j 1))
           (equal (equal 0 (land i j 1))
                  (or (equal i 0)
                      (equal j 0)))))

;make alt version?
(defthm land-bnd
  (implies (case-split (<= 0 x))
           (<= (land x y n) x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable land))))

#|
;move?
;BOZO yuck! logand is in the conclusion!
;BOZO different from lior-shift (only 1 arg is shifted).  consider renaming?
;BOZO drop fl from conclusion?
;could tighten n to m first, then drop the irrelevant term?
(defthm land-shift
  (implies (and (not (zp n))
                (natp m)
                (<= m n)
                (bvecp y m)
                (bvecp x (- n m)))
           (= (land (* (expt 2 m) x) y n)
              (* (expt 2 m) (logand x (fl (/ y (expt 2 m)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-expt (n m)))
           :in-theory (enable bvecp-forward bvecp-shift-up bits-tail land))))

;try
(defthm land-shift-2
  (implies (and (not (zp n))
                (natp m)
                (<= m n)
                (bvecp y m)
                (bvecp x (- n m)))
           (= (land (* (expt 2 m) x) y n)
              0))
  :rule-classes ()
  :hints (("Goal" :use (land-shift (:instance fl-unique (x (* Y (/ (EXPT 2 M)))) (n 0)))
           :in-theory (e/d  (bvecp) ( FL-EQUAL-0)))))
|#

(local
 (defthmd land-with-shifted-arg-helper
  (implies (and (bvecp x (- n m)) ;dropped below
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land x (bits y (1- n) m) (+ n (- m))))))
  :hints (("Goal" :use ((:instance logand-expt (n m) (y (fl (MOD Y (EXPT 2 N))))))
           :in-theory (enable land bits bvecp)))))

;enable? make an alt version??
(defthmd land-ignores-bits
  (equal (land (bits x (1- n) 0) y n)
         (land x y n))
  :hints (("Goal" :in-theory (enable land))))

(defthmd land-with-shifted-arg
  (implies (and (integerp x) ;gen?
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land x (bits y (1- n) m) (+ n (- m))))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable expt-split expt-minus bvecp)
           :use ((:instance land-ignores-bits (y (BITS Y (+ -1 N) M)) (n (+ N (* -1 M))))
                 (:instance land-ignores-bits (x (* X (EXPT 2 M))))
                 (:instance land-with-shifted-arg-helper (x (bits x (+ -1 n (- m)) 0)))))))




#|
;try
(defthm land-shift-4
  (implies (and (not (zp n))
                (natp m)
                (<= m n)
                (integerp y)
                (<= 0 y)
                ;(bvecp y m)
;                (bvecp x (- n m))
                )
           (= (land (* (expt 2 m) x) y n)
              (* (expt 2 m)
                 (land (bits x (+ -1 n (- m)) 0)
                       (bits y (1- n) m)
                       (+ n (- m))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-expt (n m) (x (bits x (+ -1 n (- m)) 0))
                                   (y (MOD Y (EXPT 2 N)))))
           :in-theory (e/d ( land bits bvecp expt-split expt-minus mod-prod)
                           (mod-does-nothing)))))
|#

(defthmd land-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (equal (land x (expt 2 k) n)
                  (* (expt 2 k) (bitn x k))))
  :hints (("Goal" :use ((:instance logand-expt-2 (x (bits x (1- n) 0)))
			(:instance expt-strong-monotone (n k) (m n)))
           :in-theory (enable bvecp land))))

(defthm land-slice
  (implies (and (< j i) ;drop?
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j)
                )
           (equal (land x (- (expt 2 i) (expt 2 j)) n)
                  (* (expt 2 j) (bits x (1- i) j))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-slice (x (bits x (1- n) 0)) (n i) (k j))
                        )
           :in-theory (enable expt-strong-monotone-linear
                              expt-weak-monotone-linear
                              land))))
(defthm land-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (land x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable land))))

(defthm land-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (land x y n) (1- (expt 2 n)))))

(defthm land-nest-tighten
  (implies (and (syntaxp (not (equal m n)))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (land x (land y z m) n)
                  (land x (land y z (min m n)) (min m n))))
  :hints (("Goal" :use (:instance and-dist-d
                                  (x (logand (BITS Y (1- M) 0)
                                             (BITS Z (1- M) 0)))
                                  (n m)
                                  (y  (BITS X (1- N) 0)))
           :in-theory (enable land))))

(defthm land-fl-1
  (equal (land (fl x) y n)
         (land x y n))
  :hints (("Goal" :in-theory (enable land))))

(defthm land-fl-2-eric
  (equal (land x (fl y) n)
         (land x y n))
  :hints (("Goal" :in-theory (enable land))))