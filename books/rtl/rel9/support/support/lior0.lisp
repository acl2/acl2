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

This book is about LIOR0, a nice version of LOGIOR.  LIOR0 takes an extra size parameter, N, and always returns
a bit vector of length N.

Todo:
add versions like logand-expt-2 and logand-expt-4 <-- huh?
prove (elsewhere) lemmas mixing lior0 with other functions
|#

;; Necessary defuns:

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

(local (include-book "lior0-proofs"))

;; Start of new stuff:

(defund binary-lior0 (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logior (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro lior0 (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior0 x y n) -- the base case
         `(binary-lior0 ,@x))
        (t
         `(binary-lior0 ,(car x)
                       (lior0 ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable lior0)) to refer to binary-lior0.
(add-macro-alias lior0 binary-lior0)

(defthm lior0-nonnegative-integer-type
  (and (integerp (lior0 x y n))
       (<= 0 (lior0 x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lior0) is no better than lior0-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lior0)))

;drop this if we plan to keep natp enabled?
(defthm lior0-natp
  (natp (lior0 x y n)))

(defthm lior0-with-n-not-a-natp
  (implies (not (natp n))
           (equal (lior0 x y n)
                  0)))

(defthmd lior0-bvecp-simple
  (bvecp (lior0 x y n) n))

(defthm lior0-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lior0 x y n) k)))


;;
;; Rules to normalize lior0 terms (recall that LIOR0 is a macro for BINARY-LIOR0):
;;

;; allow sizes to differ on these?

(defthm lior0-associative
  (equal (lior0 (lior0 x y n) z n)
         (lior0 x (lior0 y z n) n)))

(defthm lior0-commutative
  (equal (lior0 y x n)
         (lior0 x y n)))

(defthm lior0-commutative-2
  (equal (lior0 y (lior0 x z n) n)
         (lior0 x (lior0 y z n) n)))

(defthm lior0-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (lior0 x (lior0 y z n) n)
                  (lior0 (lior0 x y n) z n))))

(defthm lior0-0
  (implies (case-split (bvecp y n))
           (equal (lior0 0 y n)
                  y)))

;nicer than the analogous rule for logior?
(defthm lior0-1
  (implies (case-split (bvecp y 1))
           (equal (lior0 1 y 1)
                  1)))

(defthm lior0-self
  (implies (and (case-split (bvecp x n))
                (case-split (integerp n)))
           (equal (lior0 x x n)
                  x)))

(defthmd bits-lior0-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lior0 x y n) i j)
                  (lior0 (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j))))))

(defthmd bits-lior0-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lior0 x y n) i j)
                  (lior0 (bits x i j)
                        (bits y i j)
                        (+ n (- j))))))

;notice the call to MIN in the conclusion
(defthm bits-lior0
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (lior0 x y n) i j)
                  (lior0 (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-lior0-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior0 x y n) m)
                  (lior0 (bitn x m)
                        (bitn y m)
                        1))))

(defthmd bitn-lior0-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior0 x y n) m)
                  0)))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-lior0
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior0 x y n) m)
                  (if (< m n)
                      (lior0 (bitn x m)
                            (bitn y m)
                            1)
                    0))))

;or could wrap bits around conclusion?
(defthm lior0-equal-0
  (implies (and (case-split (bvecp x n))
                (case-split (bvecp y n))
                (case-split (integerp n))
                )
           (equal (equal 0 (lior0 x y n))
                  (and (equal x 0)
                       (equal y 0)))))

(defthm lior0-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (lior0 x y 1))
                  (and (equal x 0)
                       (equal y 0)))))

(defthm lior0-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (lior0 x y 1))
                  (or (equal x 1)
                      (equal y 1)))))

(defthm lior0-ones
  (implies (and (case-split (bvecp x n))
                (case-split (natp n)) ;gen
                )
           (equal (lior0 (1- (expt 2 n)) x n)
                  (1- (expt 2 n))))
  :rule-classes ())

;lior0-with-all-ones will rewrite (lior0 x n) [note there's only one value being ANDed], because (lior0 x n)
;expands to (BINARY-LIOR0 X (ALL-ONES N) N) - now moot???
(defthm lior0-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (lior0 (all-ones n) x n)
                  (all-ones n))))

(defthm lior0-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
		(case-split (natp n))
                (case-split (bvecp x n)))
           (equal (lior0 k x n)
                  (1- (expt 2 n)))))

(defthm lior0-def
    (implies (and (< 0 n)
		  (integerp n))
	     (equal (lior0 x y n)
		    (+ (* 2 (lior0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
		       (lior0 (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthm lior0-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (lior0 x y n) 2)
		    (lior0 (mod x 2) (mod y 2) 1))))

(defthm lior0-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (lior0 x y n) 2))
		    (lior0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

(in-theory (disable lior0-mod-2 lior0-fl-2))

;BOZO rename
(defthm lior0-x-y-0
  (equal (lior0 x y 0) 0))

(defthm lior0-reduce
  (implies (and (bvecp x n)
                (bvecp y n)
                (< n m)
                (natp n) ;gen?
                (natp m)
                )
           (equal (lior0 x y m) (lior0 x y n))))

;whoa! this is a *lower* bound !
;make alt version?
(defthm lior0-bnd
  (implies (case-split (bvecp x n))
           (<= x (lior0 x y n)))
  :rule-classes (:rewrite :linear))

;get rid of the bvecp hyps (do that for many lemmas like this one)
(defthm lior0-with-shifted-arg
    (implies (and (bvecp y m)
		  (bvecp x (- n m))
                  (<= m n)
		  (natp m)
                  (integerp n)
                  )
	     (= (lior0 (* (expt 2 m) x) y n)
		(+ (* (expt 2 m) x) y)))
  :rule-classes ())

(defthm lior0-shift
    (implies (and (bvecp x (- n m))
		  (bvecp y (- n m))
                  (integerp n) ;(not (zp n))
		  (natp m)
		  (<= m n)
                  )
	     (= (lior0 (* (expt 2 m) x)
		      (* (expt 2 m) y)
		      n)
		(* (expt 2 m) (lior0 x y (- n m)))))
  :rule-classes ())

(defthm lior0-expt-original
    (implies (and (natp n)
		  (natp k)
		  (< k n)
		  (bvecp x n))
	     (= (lior0 x (expt 2 k) n)
		(+ x (* (expt 2 k) (- 1 (bitn x k))))))
  :rule-classes ())

(defthm lior0-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (= (lior0 x (expt 2 k) n)
              (+ (bits x (1- n) 0)
                 (* (expt 2 k) (- 1 (bitn x k))))))
  :rule-classes ())

;interesting.  not the same as lior0-bvecp (here, m can be smaller than n)
;rename !!
(defthm lior0-bvecp-2
  (implies (and (bvecp x m)
                (bvecp y m)
                )
           (bvecp (lior0 x y n) m)))

(defthm lior0-upper-bound
  (< (lior0 x y n) (expt 2 n))
  :rule-classes (:rewrite :linear))

(defthm lior0-upper-bound-tight
  (implies (<= 0 n)
           (<= (lior0 x y n) (1- (expt 2 n))))
  :rule-classes (:rewrite :linear))

(defthm lior0-fl-1
  (equal (lior0 (fl x) y n)
         (lior0 x y n)))

(defthm lior0-fl-2-eric
  (equal (lior0 x (fl y) n)
         (lior0 x y n)))

(defthmd lior0-bits-1
  (equal (lior0 (bits x (1- n) 0)
               y
               n)
         (lior0 x y n)))

(defthmd lior0-bits-2
  (equal (lior0 x
               (bits y (1- n) 0)
               n)
         (lior0 x y n)))

(defthm lior0-base
  (equal (lior0 x y 1)
         (if (or (equal (bitn x 0) 1)
                 (equal (bitn y 0) 1))
             1
           0))
  :rule-classes nil)
