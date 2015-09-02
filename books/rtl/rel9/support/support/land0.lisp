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

(in-package "ACL2")

#|

This book is about LAND0, a nice version of LOGAND.  LAND0 takes an extra size parameter, N, and always returns
a bit vector of length N.

Todo:
add versions of logand-expt-2 and logand-expt-4
prove (elsewhere) lemmas mixing land0 with other functions

|#

;;Necessary defuns:

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

(local (include-book "land0-proofs"))

;; New stuff

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

;BOZO split into 2 rules?
(defthm land0-with-n-not-a-natp
  (implies (not (natp n))
           (equal (land0 x y n)
                  0)))

(defthmd land0-bvecp-simple
  (bvecp (land0 x y n) n))

(defthm land0-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (land0 x y n) k)))


;;
;; Rules to normalize land0 terms (recall that LAND0 is a macro for BINARY-LAND0):
;;

;This guarantees that the n parameters to nested LAND0 calls match.
;Note the MIN in the conclusion.
;BOZO do we expect MIN to be enabled?  Maybe we should use IF instead for this and other rules?
(defthm land0-nest-tighten
  (implies (and (syntaxp (not (equal m n)))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (land0 x (land0 y z m) n)
                  (land0 x (land0 y z (min m n)) (min m n)))))

; allow the n's to differ on this?
(defthm land0-associative
  (equal (land0 (land0 x y n) z n)
         (land0 x (land0 y z n) n)))

(defthm land0-commutative
  (equal (land0 y x n)
         (land0 x y n)))

; allow the n's to differ on this?
(defthm land0-commutative-2
  (equal (land0 y (land0 x z n) n)
         (land0 x (land0 y z n) n)))

; allow the n's to differ on this?
(defthm land0-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (land0 x (land0 y z n) n)
                  (land0 (land0 x y n) z n))))

(defthm land0-0
  (equal (land0 0 y n)
         0))

;nicer than the analogous rule for logand? is it really?
;BOZO gen the second 1 in the lhs?
(defthm land0-1
  (equal (land0 1 y 1)
         (bitn y 0)))

(defthm land0-self
  (equal (land0 x x n)
         (bits x (1- n) 0)))

;perhaps use only the main rule, bits-land0?
(defthmd bits-land0-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land0 x y n) i j)
                  (land0 (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j))))))

;perhaps use only the main rule, bits-land0?
(defthmd bits-land0-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land0 x y n) i j)
                  (land0 (bits x i j)
                        (bits y i j)
                        (+ n (- j))))))

;Notice the call to MIN in the conclusion.
(defthm bits-land0
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (land0 x y n) i j)
                  (land0 (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-land0-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land0 x y n) m)
                  (land0 (bitn x m)
                        (bitn y m)
                        1))))
(defthmd bitn-land0-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land0 x y n) m)
                  0)))

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
                    0))))

;BOZO see land0-equal-0
;drop bvecp hyps and put bitn in conclusion?
(defthm land0-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (land0 x y 1))
                  (or (equal x 0)
                      (equal y 0)))))

(defthm land0-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (land0 x y 1))
                  (and (equal x 1)
                       (equal y 1)))))

(defthm land0-ones
  (equal (land0 (1- (expt 2 n)) x n)
         (bits x (1- n) 0))
  :rule-classes ())

;land0-with-all-ones will rewrite (land0 x n) [note there's only one value being ANDed], because (land0 x n)
;expands to (BINARY-LAND0 X (ALL-ONES N) N) - now moot???
;BOZO drop bvecp hyp and move to conclusion?
(defthm land0-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (land0 (all-ones n) x n)
                  x)))

(defthmd land0-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (equal k (1- (expt 2 n))) ;this computes on constants...
                )
           (equal (land0 k x n)
                  (bits x (1- n) 0))))

(defthm land0-def
  (implies (and (> n 0)
                (integerp n))
           (equal (land0 x y n)
                  (+ (* 2 (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land0 (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthmd land0-mod-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (mod (land0 x y n) 2)
                  (land0 (mod x 2) (mod y 2) 1))))

;BOZO RHS isn't simplified...
(defthmd land0-fl-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (fl (/ (land0 x y n) 2))
                  (land0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

;BOZO rename to land0-with-n-0
;what if n is negative? or not an integer?
(defthm land0-x-y-0
  (equal (land0 x y 0) 0))

;actually, maybe only either x or y must be a bvecp of length n
;n is a free var
(defthm land0-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land0 x y m)
                    (land0 x y n))))

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
  :rule-classes (:rewrite :linear))

;enable? make an alt version??
(defthmd land0-ignores-bits
  (equal (land0 (bits x (1- n) 0) y n)
         (land0 x y n)))

(defthmd land0-with-shifted-arg
  (implies (and (integerp x) ;gen?
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land0 (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land0 x (bits y (1- n) m) (+ n (- m)))))))

(defthmd land0-shift
  (implies (and (integerp x)
                (integerp y) ; actually (rationalp y) works
                (natp k))
           (= (land0 (* (expt 2 k) x)
                     (* (expt 2 k) y)
                     n)
              (* (expt 2 k) (land0 x y (- n k))))))

(defthmd land0-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (equal (land0 x (expt 2 k) n)
                  (* (expt 2 k) (bitn x k)))))

(defthm land0-slice
  (implies (and (<= j i) ;drop? or not?
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j)
                )
           (equal (land0 x (- (expt 2 i) (expt 2 j)) n)
                  (* (expt 2 j) (bits x (1- i) j))))
  :rule-classes ())

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
                    (- (expt 2 n) (expt 2 k))))))

(defthm land0-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (land0 x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear))

(defthm land0-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (land0 x y n) (1- (expt 2 n)))))

(defthm land0-fl-1
  (equal (land0 (fl x) y n)
         (land0 x y n)))

(defthm land0-fl-2-eric ;BOZO name conflicted...
  (equal (land0 x (fl y) n)
         (land0 x y n)))

(defthmd land0-bits-1
  (equal (land0 (bits x (1- n) 0)
               y
               n)
         (land0 x y n)))

(defthmd land0-bits-2
  (equal (land0 x
               (bits y (1- n) 0)
               n)
         (land0 x y n)))

(defthm land0-base
  (equal (land0 x y 1)
         (if (and (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             1
           0))
  :rule-classes nil)
