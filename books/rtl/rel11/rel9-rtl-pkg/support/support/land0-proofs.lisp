; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

#|

This book is about LAND0, a nice version of LOGAND.  LAND0 takes an extra size parameter, N, and always returns
a bit vector of length N.

Todo:
add versions of logand-expt-2 and logand-expt-4
prove (elsewhere) lemmas mixing land0 with other functions
what should land0 of non-ints be?

think about removing bits from defn of land0? why???
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
(local (include-book "../../arithmetic/top"))

;We expect n to be a positive integer, and x and y to be bit vectors of length n.
(defund binary-land0 (x y n)
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

(defmacro land0 (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(land0 x y n) -- the base case
         `(binary-land0 ,@x))
        (t
         `(binary-land0 ,(car x)
                       (land0 ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable land0)) to refer to binary-land0.
(add-macro-alias land0 binary-land0)

(defthm land0-nonnegative-integer-type
  (and (integerp (land0 x y n))
       (<= 0 (land0 x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription land0) is no better than land0-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-land0)))

;drop this if we plan to keep natp enabled?
(defthm land0-natp
  (natp (land0 x y n)))

(defthm land0-with-n-not-a-natp
  (implies (not (natp n))
           (equal (land0 x y n)
                  0))
  :hints (("Goal" :cases ((acl2-numberp n))
           :in-theory (enable land0)))
  )

(defthmd land0-bvecp-simple
  (bvecp (land0 x y n) n)
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable land0))))

(defthm land0-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (land0 x y n) k))
  :hints (("Goal" :in-theory (disable land0-bvecp-simple)
           :use land0-bvecp-simple)))


;;
;; Rules to normalize land0 terms (recall that LAND0 is a macro for BINARY-LAND0):
;;

;; allow sizes to differ on these?

(defthm land0-associative
  (equal (land0 (land0 x y n) z n)
         (land0 x (land0 y z n) n))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable land0 bits-tail))))

#|
;move
(defthm logand-tighten-helper
  (implies (bvecp x m)
           (equal (logand x y)
                  (logand (bits x (1- m) 0) y))))

(defthm land0-tighten-1
  (implies (and (< m n)
                (integerp m)
                (integerp n))
           (equal (land0 (land0 x y m) z n)
                  (land0 (land0 x y m) z m)))
  :hints (("Goal" :in-theory (enable bits-tail)
           :expand ((BINARY-LAND0 Z (BINARY-LAND0 X Y M) N)))))


(defthm land0-associative-gen
  (implies (and (integerp m)
                (integerp n)
                (<= 0 m)
                (<= 0 n)
                (<= m n)
;                (bvecp x m)
;                (bvecp z n)
                )
  (equal (land0 (land0 x y m) z n)
         (land0 x (land0 y z m) m)))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable land0 bits-tail))))
  |#

(defthm land0-commutative
  (equal (land0 y x n)
         (land0 x y n))
  :hints (("Goal" :in-theory (enable land0))))

;gen (must the n's match)?
(defthm land0-commutative-2
  (equal (land0 y (land0 x z n) n)
         (land0 x (land0 y z n) n))
  :hints (("Goal"  :cases ((natp n))
           :in-theory (enable land0 bits-tail))))

(defthm land0-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (land0 x (land0 y z n) n)
                  (land0 (land0 x y n) z n))))


(defthm land0-0
  (equal (land0 0 y n)
         0)
  :hints (("Goal" :in-theory (enable land0))))

;nicer than the analogous rule for logand?
;would like to let the 1 be any n?
(defthm land0-1
  (equal (land0 1 y 1)
         (bitn y 0))
  :hints (("Goal" :in-theory (enable land0 bitn))))

(defthm land0-self
  (equal (land0 x x n)
         (bits x (1- n) 0))
  :hints (("Goal" :in-theory (enable land0 bits-tail))))

(defthmd bits-land0-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land0 x y n) i j)
                  (land0 (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable land0 bits-logand))))


(defthmd bits-land0-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land0 x y n) i j)
                  (land0 (bits x i j)
                        (bits y i j)
                        (+ n (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable land0 bits-logand))))

;notice the call to MIN in the conclusion
(defthm bits-land0
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (land0 x y n) i j)
                  (land0 (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j)))))
  :hints (("Goal" :in-theory (enable bits-land0-1 bits-land0-2))))

(defthmd bitn-land0-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land0 x y n) m)
                  (land0 (bitn x m)
                        (bitn y m)
                        1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '(BITS-N-N-REWRITE)))))
(defthmd bitn-land0-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land0 x y n) m)
                  0))
  :hints (("Goal" :in-theory (enable bvecp-bitn-0))))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-land0
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land0 x y n) m)
                  (if (< m n)
                      (land0 (bitn x m)
                            (bitn y m)
                            1)
                    0)))
  :hints (("Goal" :in-theory (enable bitn-land0-1 bitn-land0-2))))

;BOZO see land0-equal-0
;drop bvecp hyps and out bitn in conclusion?
(defthm land0-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (land0 x y 1))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))

(defthm land0-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (land0 x y 1))
                  (and (equal x 1)
                       (equal y 1))))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))



;in general, rewrite (bvecp k n) where k is a constant to a fact about n

;BOZO allow the n's to differ?
(defthm land0-ones
  (equal (land0 (1- (expt 2 n)) x n)
         (bits x (1- n) 0))
  :rule-classes ()
  :hints (("goal" :cases ((natp n))
           :in-theory (enable land0 bits-tail logand-ones bvecp)
           )))

#| old:
(defthm land0-ones
  (implies (case-split (bvecp x n))
           (equal (land0 (1- (expt 2 n)) x n)
                  x))
  :rule-classes ()
  :hints (("goal" :cases ((natp n))
           :in-theory (enable land0 bits-tail logand-ones bvecp)
           )))
|#

;land0-with-all-ones will rewrite (land0 x n) [note there's only one value being ANDed], because (land0 x n)
;expands to (BINARY-LAND0 X (ALL-ONES N) N) - now moot???
(defthm land0-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (land0 (all-ones n) x n)
                  x))
  :hints (("goal" :use land0-ones
           :in-theory (enable all-ones))))

#| old
(defthm land0-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
                (case-split (bvecp x n)))
           (equal (land0 k x n)
                  x))
  :hints (("Goal" :use land0-ones)))
|#

(defthmd land0-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (equal k (1- (expt 2 n))) ;this computes on constants...
                )
           (equal (land0 k x n)
                  (bits x (1- n) 0)))
  :hints (("Goal" :use (:instance land0-ones))))


(local (in-theory (disable mod-by-2-rewrite-to-even mod-mult-of-n mod-equal-0 )))

(encapsulate
 ()

 (local
  (defthm land0-def-integerp
    (implies (and (integerp x)
                  (integerp y)
                  (> n 0)
                  (integerp n))
             (equal (land0 x y n)
                    (+ (* 2 (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (land0 (mod x 2) (mod y 2) 1))))
    :rule-classes ()
    :hints (("Goal" :in-theory (e/d (land0 bits-fl-by-2) ())
             :use ((:instance logand-rewrite (x (bits x (1- n) 0)) (y (bits y (1- n) 0)))
                   (:instance mod012 (m x))
                   (:instance mod012 (m y)))))))

; Now we want to eliminate the (integerp x) and (integerp y) hypotheses from
; land0-def-integerp.  First suppose x is not rational.

 (local
  (defthm land0-is-0-if-not-rational
    (implies (not (rationalp x))
             (and (equal (land0 x y n) 0)
                  (equal (land0 y x n) 0)))
    :hints (("Goal" :expand ((land0 x y n)
                             (land0 y x n))))))

 (local
  (defthm fl-1/2-is-0-if-not-rational
    (implies (not (rationalp x))
             (equal (fl (* 1/2 x)) 0))
    :hints (("Goal" :cases ((acl2-numberp x))))))

 (local
  (defthm mod-2-if-not-rational
    (implies (not (rationalp x))
             (equal (mod x 2)
                    (fix x)))
    :hints (("Goal" :expand ((mod x 2))))))

 (local
  (defthm land0-def-not-rational
    (implies (and (or (not (rationalp x))
                      (not (rationalp y)))
                  (> n 0)
                  (integerp n))
             (equal (land0 x y n)
                    (+ (* 2 (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (land0 (mod x 2) (mod y 2) 1))))
    :rule-classes nil))

 (local
  (defthm land0-fl-1
    (equal (land0 (fl x) y n)
           (land0 x y n))
    :hints (("Goal" :expand ((land0 y (fl x) n)
                             (land0 x y n))))))

 (local
  (defthm land0-fl-2
    (equal (land0 y (fl x) n)
           (land0 y x n))
    :hints (("Goal" :expand ((land0 y (fl x) n)
                             (land0 x y n))))))

 (local
  (defthm land0-def-rational-hack
    (implies (and (rationalp x)
                  (rationalp y)
                  (>= n 0)
                  (integerp n))
             (equal (land0 (* 1/2 (fl x)) (* 1/2 (fl y)) n)
                    (land0 (* 1/2 x) (* 1/2 y) n)))
    :hints (("Goal" :expand ((land0 (* 1/2 (fl x)) (* 1/2 (fl y)) n)
                             (land0 (* 1/2 x) (* 1/2 y) n))))))

 (local
  (defthm land0-def-rational
    (implies (and (rationalp x)
                  (rationalp y)
                  (> n 0)
                  (integerp n))
             (equal (land0 x y n)
                    (+ (* 2 (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (land0 (mod x 2) (mod y 2) 1))))
    :rule-classes ()
    :hints (("Goal"
             :use ((:instance land0-def-integerp (x (fl x)) (y (fl y))))
             :in-theory (e/d (mod-fl-eric) (fl-mod))))))

 (defthm land0-def
   (implies (and (> n 0)
                 (integerp n))
            (equal (land0 x y n)
                   (+ (* 2 (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                      (land0 (mod x 2) (mod y 2) 1))))
   :rule-classes ()
   :hints (("Goal" :use (land0-def-not-rational land0-def-rational)))))

(defthm land0-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (land0 x y n) 2)
		    (land0 (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use (land0-def
			(:instance mod012 (m x))
			(:instance mod012 (m y))
			(:instance quot-mod (m (land0 x y n)) (n 2))))))

(defthm land0-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (land0 x y n) 2))
		    (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use (land0-def
			(:instance mod012 (m x))
			(:instance mod012 (m y))
			(:instance quot-mod (m (land0 x y n)) (n 2))))))

(in-theory (disable land0-mod-2 land0-fl-2))

;BOZO rename to land0-with-n-0
;what if n is negative? or not an integer?
(defthm land0-x-y-0
    (equal (land0 x y 0) 0)
  :hints (("Goal" :in-theory (enable land0))))

;actually, maybe only either x or y must be a bvecp of length n
;n is a free var
(defthm land0-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land0 x y m)
                    (land0 x y n)))
  :hints (("Goal" :in-theory (enable land0))))

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
(defthm land0-equal-0
  (implies (and (bvecp i 1)
                (bvecp j 1))
           (equal (equal 0 (land0 i j 1))
                  (or (equal i 0)
                      (equal j 0)))))

;make alt version?
(defthm land0-bnd
  (implies (case-split (<= 0 x))
           (<= (land0 x y n) x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable land0))))

#|
;move?
;BOZO yuck! logand is in the conclusion!
;BOZO different from lior0-shift (only 1 arg is shifted).  consider renaming?
;BOZO drop fl from conclusion?
;could tighten n to m first, then drop the irrelevant term?
(defthm land0-shift
  (implies (and (not (zp n))
                (natp m)
                (<= m n)
                (bvecp y m)
                (bvecp x (- n m)))
           (= (land0 (* (expt 2 m) x) y n)
              (* (expt 2 m) (logand x (fl (/ y (expt 2 m)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-expt (n m)))
           :in-theory (enable bvecp-forward bvecp-shift-up bits-tail land0))))

;try
(defthm land0-shift-2
  (implies (and (not (zp n))
                (natp m)
                (<= m n)
                (bvecp y m)
                (bvecp x (- n m)))
           (= (land0 (* (expt 2 m) x) y n)
              0))
  :rule-classes ()
  :hints (("Goal" :use (land0-shift (:instance fl-unique (x (* Y (/ (EXPT 2 M)))) (n 0)))
           :in-theory (e/d  (bvecp) ( FL-EQUAL-0)))))
|#

(local
 (defthmd land0-with-shifted-arg-helper
  (implies (and (bvecp x (- n m)) ;dropped below
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land0 (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land0 x (bits y (1- n) m) (+ n (- m))))))
  :hints (("Goal" :use ((:instance logand-expt (n m) (y (fl (MOD Y (EXPT 2 N))))))
           :in-theory (enable land0 bits bvecp)))))

;enable? make an alt version??
(defthmd land0-ignores-bits
  (equal (land0 (bits x (1- n) 0) y n)
         (land0 x y n))
  :hints (("Goal" :in-theory (enable land0))))

(defthmd land0-with-shifted-arg
  (implies (and (integerp x) ;gen?
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land0 (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land0 x (bits y (1- n) m) (+ n (- m))))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable expt-split expt-minus bvecp)
           :use ((:instance land0-ignores-bits (y (BITS Y (+ -1 N) M)) (n (+ N (* -1 M))))
                 (:instance land0-ignores-bits (x (* X (EXPT 2 M))))
                 (:instance land0-with-shifted-arg-helper (x (bits x (+ -1 n (- m)) 0)))))))

(defthmd land0-shift
  (implies (and (integerp x)
                (integerp y) ; actually (rationalp y) works
                (natp k))
           (= (land0 (* (expt 2 k) x)
                     (* (expt 2 k) y)
                     n)
              (* (expt 2 k) (land0 x y (- n k)))))
  :hints (("Goal" :use ((:instance land0-with-shifted-arg
                                   (m k)
                                   (x x)
                                   (y (* (expt 2 k) y))
                                   (n n))
                        (:instance land0-ignores-bits (x y)
                                   (y x)
                                   (n (- n k)))))))


#|
;try
(defthm land0-shift-4
  (implies (and (not (zp n))
                (natp m)
                (<= m n)
                (integerp y)
                (<= 0 y)
                ;(bvecp y m)
;                (bvecp x (- n m))
                )
           (= (land0 (* (expt 2 m) x) y n)
              (* (expt 2 m)
                 (land0 (bits x (+ -1 n (- m)) 0)
                       (bits y (1- n) m)
                       (+ n (- m))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-expt (n m) (x (bits x (+ -1 n (- m)) 0))
                                   (y (MOD Y (EXPT 2 N)))))
           :in-theory (e/d ( land0 bits bvecp expt-split expt-minus mod-prod)
                           (mod-does-nothing)))))
|#

(defthmd land0-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (equal (land0 x (expt 2 k) n)
                  (* (expt 2 k) (bitn x k))))
  :hints (("Goal" :use ((:instance logand-expt-2 (x (bits x (1- n) 0)))
			(:instance expt-strong-monotone (n k) (m n)))
           :in-theory (enable bvecp land0))))

(defthm land0-slice
  (implies (and (<= j i) ;drop?
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j)
                )
           (equal (land0 x (- (expt 2 i) (expt 2 j)) n)
                  (* (expt 2 j) (bits x (1- i) j))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-slice (x (bits x (1- n) 0)) (n i) (k j))
                        )
           :in-theory (enable expt-strong-monotone-linear
                              expt-weak-monotone-linear
                              land0))))
; Start proof of land-slices.

(local
 (defthm land0-slices-1
   (implies (and (natp n)
                 (natp l)
                 (natp k)
                 (<= l k)
                 (< k n))
            (equal (land0 (- (expt 2 n) (1+ (expt 2 l)))
                          (- (expt 2 n) (expt 2 k))
                          n)
                   (* (expt 2 k)
                      (bits (- (expt 2 n) (1+ (expt 2 l))) (1- n) k))))
   :hints (("Goal" :use ((:instance land0-slice
                                    (x (- (expt 2 n) (1+ (expt 2 l))))
                                    (i n)
                                    (j k)
                                    (n n)))))
   :rule-classes nil))

(local
 (defthmd land0-slices-2
   (implies (and (natp n)
                 (natp l)
                 (natp k)
                 (<= l k)
                 (< k n))
            (equal (* (expt 2 k)
                      (bits (- (expt 2 n) (1+ (expt 2 l))) (1- n) k))
                   (* (expt 2 k)
                      (fl (/ (- (expt 2 n) (1+ (expt 2 l))) (expt 2 k))))))
   :instructions (:promote (:dv 1)
                           (:dv 2)
                           :x :top (:dv 1 2 1 2 0)
                           (:rewrite mod-does-nothing)
                           :top :prove :prove
                           (:use (:instance expt-strong-monotone (n l)
                                            (m n)))
                           (:in-theory (disable expt-compare power2p-expt2-i))
                           :bash)))

(local
 (defthmd land0-slices-3
   (implies (and (natp n)
                 (natp l)
                 (natp k)
                 (<= l k)
                 (< k n))
            (equal (* (expt 2 k)
                      (fl (/ (- (expt 2 n) (1+ (expt 2 l))) (expt 2 k))))
                   (* (expt 2 k)
                      (+ (expt 2 (- n k))
                         (fl (/ (- (1+ (expt 2 l))) (expt 2 k)))))))
   :hints (("Goal" :use ((:instance fl+int-rewrite
                                    (x (/ (1+ (expt 2 l)) (expt 2 k)))
                                    (n (/ (expt 2 n) (expt 2 k)))))))))

(local (include-book "../../arithmetic/fl-hacks"))

(local
 (defthmd land0-slices-4
   (implies (and (natp n)
                 (natp l)
                 (natp k)
                 (<= l k)
                 (< k n))
            (equal (* (expt 2 k)
                      (+ (expt 2 (- n k))
                         (fl (/ (- (1+ (expt 2 l))) (expt 2 k)))))
                   (* (expt 2 k)
                      (+ (expt 2 (- n k))
                         (- (fl (/ (expt 2 l) (expt 2 k))))
                         -1))))
   :hints (("Goal" :use ((:instance fl-m-n
                                    (m (1+ (expt 2 l)))
                                    (n (expt 2 k))))))))

(local
 (defthmd land0-slices-5
   (implies (and (natp n)
                 (natp l)
                 (natp k)
                 (<= l k)
                 (< k n))
            (equal (* (expt 2 k)
                      (+ (expt 2 (- n k))
                         (- (fl (/ (expt 2 l) (expt 2 k))))
                         -1))
                   (- (expt 2 n)
                      (* (expt 2 k)
                         (1+ (fl (/ (expt 2 l) (expt 2 k))))))))))

(defthmd land0-slices
  (implies (and (natp n)
                (natp l)
                (natp k)
                (<= l k)
                (< k n))
           (equal (land0 (- (expt 2 n) (1+ (expt 2 l)))
                         (- (expt 2 n) (expt 2 k))
                         n)
                  (if (= l k)
                      (- (expt 2 n) (expt 2 (1+ k)))
                    (- (expt 2 n) (expt 2 k)))))
  :instructions ((:use land0-slices-1
                       land0-slices-2 land0-slices-3
                       land0-slices-4 land0-slices-5)
                 :promote (:dv 1)
                 := (:drop 1)
                 := (:drop 1)
                 := (:drop 1)
                 := (:drop 1)
                 := (:drop 1)
                 :top :prove))

(defthm land0-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (land0 x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable land0))))

(defthm land0-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (land0 x y n) (1- (expt 2 n)))))

(defthm land0-nest-tighten
  (implies (and (syntaxp (not (equal m n)))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (land0 x (land0 y z m) n)
                  (land0 x (land0 y z (min m n)) (min m n))))
  :hints (("Goal" :use (:instance and-dist-d
                                  (x (logand (BITS Y (1- M) 0)
                                             (BITS Z (1- M) 0)))
                                  (n m)
                                  (y  (BITS X (1- N) 0)))
           :in-theory (enable land0))))

(defthm land0-fl-1
  (equal (land0 (fl x) y n)
         (land0 x y n))
  :hints (("Goal" :in-theory (enable land0))))

(defthm land0-fl-2-eric
  (equal (land0 x (fl y) n)
         (land0 x y n))
  :hints (("Goal" :in-theory (enable land0))))

(defthmd land0-bits-1
  (equal (land0 (bits x (1- n) 0)
               y
               n)
         (land0 x y n))
  :hints (("Goal" :in-theory (e/d (land0) (logior land0-commutative)))))

(defthmd land0-bits-2
  (equal (land0 x
               (bits y (1- n) 0)
               n)
         (land0 x y n))
  :hints (("Goal" :in-theory (e/d (land0) (logior land0-commutative)))))

(local
 (defthm land0-base-lemma
   (implies (and (bvecp x 1) (bvecp y 1))
            (equal (land0 x y 1)
                   (if (and (equal (bitn x 0) 1)
                            (equal (bitn y 0) 1))
                       1
                     0)))
   :rule-classes nil))

(defthm land0-base
  (equal (land0 x y 1)
         (if (and (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use ((:instance land0-base-lemma
                                   (x (bits x 0 0))
                                   (y (bits y 0 0)))
                        (:instance land0-bits-1
                                   (x x)
                                   (y (bits y 0 0))
                                   (n 1))
                        (:instance land0-bits-2 (n 1)))))
  :rule-classes nil)
