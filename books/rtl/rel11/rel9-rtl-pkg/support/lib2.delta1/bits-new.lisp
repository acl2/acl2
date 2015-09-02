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

(set-enforce-redundancy t)

(include-book "../lib2/basic")

(local (include-book "bits-new-proofs"))

;; It is important that we don't have export a definition of "bits",
;; "bitn".
;;
;; eventually we will add a wrapper to redefine "bits_alt" as new "bits"
;;                                              "bitn_alt" as new "bitn"
;;

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;;;**********************************************************************
;;;				BVECP
;;;**********************************************************************

;;; Thu Feb  5 09:13:20 2009. no change from lib2/bits.lisp


(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defthm bvecp-forward
  (implies (bvecp x k)
	   (and (integerp x)
		(<= 0 x)
		(< x (expt 2 k))))
  :rule-classes :forward-chaining)

(defthmd bvecp-monotone
    (implies (and (bvecp x n)
		  (<= n m)
		  (case-split (integerp m)))
	     (bvecp x m)))

(defthmd bvecp-shift-down
    (implies (and (bvecp x n)
		  (natp n)
		  (natp k))
	     (bvecp (fl (/ x (expt 2 k))) (- n k))))

(defthmd bvecp-shift-up
    (implies (and (bvecp x (- n k))
		  (natp k)
		  (integerp n))
	     (bvecp (* x (expt 2 k)) n)))

(defthm bvecp-product
    (implies (and (bvecp x m)
		  (bvecp y n))
	     (bvecp (* x y) (+ m n)))
  :rule-classes ())

(defthmd bvecp-1-rewrite
  (equal (bvecp x 1)
	 (or (equal x 0) (equal x 1))))

(defthm bvecp-1-0
  (implies (and (bvecp x 1)
		(not (equal x 1)))
	   (equal x 0))
  :rule-classes :forward-chaining)

(defthm bvecp-0-1
  (implies (and (bvecp x 1)
		(not (equal x 0)))
	   (equal x 1))
  :rule-classes :forward-chaining)


;;;**********************************************************************
;;;			    BITS_ALT
;;;**********************************************************************

;;;
;;; Thu Feb  5 09:13:43 2009. new definition for bits
;;;
;;; later we will redefine bits to have the same definition of bits_alt.
;;;

(defund bits_alt (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))




(defthm bits_alt-nonnegative-integerp-type
  (and (<= 0 (bits_alt x i j))
       (integerp (bits_alt x i j)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription bits_alt)))

(defthm bits_alt-bvecp
    (implies (and (<= (+ 1 i (- j)) k)
		  (case-split (integerp k)))
	     (bvecp (bits_alt x i j) k)))

;;Here is a variation of bits_alt-bvecp that is less general but does not
;;require an integerp hypothesis:
(defthm bits_alt-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits_alt x i j) k)))

(defthm mod-bits_alt-equal
  (implies (= (mod x (expt 2 (1+ i)))
	      (mod y (expt 2 (1+ i))))
	   (= (bits_alt x i j) (bits_alt y i j)))
  :rule-classes ())

(defthmd mod-bits_alt-equal-cor
    (implies (and (integerp x)
		  (integerp n)
		  (integerp i)
		  (integerp j)
		  (< i n))
	     (equal (bits_alt (mod x (expt 2 n)) i j)
		    (bits_alt x i j))))

(defthmd bits_alt-mod
  (implies (and (case-split (integerp x))
		(case-split (integerp i)))
	   (equal (bits_alt x i 0)
		  (mod x (expt 2 (1+ i))))))

(defthmd bits_alt-bits_alt-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i))
	   (equal (bits_alt (+ (bits_alt x i 0) y) i 0)
		  (bits_alt (+ x y) i 0))))

(defthmd bits_alt-mod-2
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits_alt x (1- i) j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- i j))
                        (fl (/ x (expt 2 i))))))))

(defthm bits_alt-neg
  (implies (and (< i 0)
                (integerp x))
           (equal (bits_alt x i j) 0)))

(defthm bits_alt-with-indices-in-the-wrong-order
  (implies (< i j)
	   (equal (bits_alt x i j)
		  0)))

(defthmd bvecp-bits_alt-0
  (implies (bvecp x j)
	   (equal (bits_alt x i j) 0)))

(defthm bits_alt-0
  (equal (bits_alt 0 i j) 0))

(defthmd neg-bits_alt-1
    (implies (and (integerp x)
		  (natp i)
		  (natp j)
		  (< x 0)
		  (>= x (- (expt 2 j)))
		  (>= i j))
	     (equal (bits_alt x i j)
                    (+ -1 (expt 2 (+ 1 i (* -1 j)))))))

(defthmd bits_alt-minus-1
    (implies (and (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits_alt -1 i j)
                    (+ -1 (expt 2 (+ 1 i (* -1 j)))))))

(defthm bits_alt-tail
  (implies (and (bvecp x (1+ i))
		(case-split (acl2-numberp i)))
	   (equal (bits_alt x i 0) x)))

(defthm bits_alt-tail-2
    (implies (and (integerp x)
		  (natp i)
		  (< x (expt 2 i))
		  (>= x (- (expt 2 (+ 1 i)))))
	     (equal (bits_alt x i 0)
		    (if (>= x 0)
			x
		      (+ x (expt 2 (+ 1 i)))))))

(defthm bits_alt-drop-from-minus
  (implies (and (bvecp x (1+ i))
                (bvecp y (1+ i))
                (<= y x)
		(case-split (acl2-numberp i)))
	   (equal (bits_alt (+ x (* -1 y)) i 0)
		  (+ x (* -1 y)))))

(defthmd bits_alt-shift-down-1
  (implies (and (<= 0 j)
		(integerp i)
		(integerp j)
		(integerp k))
	   (equal (bits_alt (fl (/ x (expt 2 k))) i j)
		  (bits_alt x (+ i k) (+ j k)))))

(defthmd bits_alt-shift-down-2
  (implies (and (integerp x)
		(natp i)
		(natp k))
	   (equal (fl (/ (bits_alt x (+ i k) 0) (expt 2 k)))
		  (bits_alt (fl (/ x (expt 2 k))) i 0))))

(defthm bits_alt-shift-up-1
  (implies (and (integerp k)
		(integerp i)
		(integerp j))
	   (equal (bits_alt (* (expt 2 k) x) i j)
		  (bits_alt x (- i k) (- j k))))
  :rule-classes ())

(defthm bits_alt-shift-up-2
  (implies (and (integerp x)
		(natp k)
		(integerp i))
	   (equal (* (expt 2 k) (bits_alt x i 0))
		  (bits_alt (* (expt 2 k) x) (+ i k) 0)))
  :rule-classes ())

(defthmd bits_alt-plus-mult-1
  (implies (and (bvecp x k)
		(<= k m)
		(integerp y)
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp k)))
	   (equal (bits_alt (+ x (* y (expt 2 k))) n m)
		  (bits_alt y (- n k) (- m k)))))

(defthm bits_alt-plus-mult-2
  (implies (and (< n k)
		(integerp y)
		(integerp k))
	   (equal (bits_alt (+ x (* y (expt 2 k))) n m)
		  (bits_alt x n m))))

(defthmd bits_alt-plus-mult-2-rewrite
   (implies (and (syntaxp (quotep c))
                 (equal (mod c (expt 2 (1+ n))) 0))
            (equal (bits_alt (+ c x) n m)
                   (bits_alt x n m))))

(defthm bits_alt-plus-bits_alt
    (implies (and (integerp m)
		  (integerp p)
		  (integerp n)
		  (<= m p)
		  (<= p n))
	     (= (bits_alt x n m)
		(+ (bits_alt x (1- p) m)
		   (* (expt 2 (- p m)) (bits_alt x n p)))))
  :rule-classes ())

(defthm bits_alt-bits_alt
  (implies (and (case-split (<= 0 l))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp l)))
	   (equal (bits_alt (bits_alt x i j) k l)
		  (if (<= k (- i j))
		      (bits_alt x (+ k j) (+ l j))
		    (bits_alt x i (+ l j))))))

;;bits_alt-match can prove things like this:
;;(thm (implies (equal 12 (bits_alt x 15 6))
;;		(equal 4 (bits_alt x 8 6))))
;;See also bits_alt-dont-match.

(defthmd bits_alt-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits_alt x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(equal k (bits_alt k2 (+ i (- j2)) (+ (- j2) j)))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits_alt x i j))
		  t)))

;;bits_alt-dont-match can prove things like this:
;;(thm (implies (equal 7 (bits_alt x 8 6))
;;		(not (equal 4 (bits_alt x 15 6)))))
;;See also bits_alt-match.

(defthmd bits_alt-dont-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits_alt x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(not (equal k (bits_alt k2 (+ i (- j2)) (+ (- j2) j))))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits_alt x i j))
		  nil)))

;;
;; Thu Feb  5 10:09:26 2009: from lib2/bits.lisp
;;

(defun bitvec (x n)
   (if (bvecp x n) x 0))

;;;**********************************************************************
;;;				BITN_ALT
;;;**********************************************************************

(defund bitn_alt (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits_alt x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defthm bitn_alt-nonnegative-integer
  (and (integerp (bitn_alt x n))
       (<= 0 (bitn_alt x n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription bitn_alt)))

(defthm bits_alt-n-n-rewrite
  (equal (bits_alt x n n)
	 (bitn_alt x n)))

(defthmd bitn_alt-def
  (implies (case-split (integerp n))
	   (equal (bitn_alt x n)
		  (mod (fl (/ x (expt 2 n))) 2))))

;;A recursive formulation:

(defthmd bitn_alt-rec-0
  (implies (integerp x)
	   (equal (bitn_alt x 0) (mod x 2))))

(defthmd bitn_alt-rec-pos
    (implies (< 0 n)
	     (equal (bitn_alt x n)
		    (bitn_alt (fl (/ x 2)) (1- n))))
  :rule-classes ((:definition :controller-alist ((bitn_alt t t)))))

;;Use this to induce case-splitting:

(defthm bitn_alt-0-1
    (or (equal (bitn_alt x n) 0)
	(equal (bitn_alt x n) 1))
  :rule-classes ())

(defthm bitn_alt-bvecp
  (implies (and (<= 1 k)
		(case-split (integerp k)))
	   (bvecp (bitn_alt x n) k)))

;;The following is a special case of bitn_alt-bvecp.
;;It is useful as a :forward-chaining rule in concert with bvecp-0-1 and
;;bvecp-1-0.
(defthm bitn_alt-bvecp-forward
  (bvecp (bitn_alt x n) 1)
  :rule-classes ((:forward-chaining :trigger-terms ((bitn_alt x n)))))

(defthm bitn_alt-neg
  (implies (and (< n 0)
                (integerp x))
           (equal (bitn_alt x n) 0)))

(defthm bitn_alt-0
  (equal (bitn_alt 0 k) 0))

(defthm bitn_alt-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn_alt x 0) x)))

(defthm bitn_alt-bitn_alt-0
    (equal (bitn_alt (bitn_alt x n) 0)
	   (bitn_alt x n)))

(defthmd bitn_alt-mod
    (implies (and (< k n)
		  (integerp n)
		  (integerp k))
	     (equal (bitn_alt (mod x (expt 2 n)) k)
		    (bitn_alt x k))))

(defthm bvecp-bitn_alt-0
    (implies (bvecp x n)
	     (equal (bitn_alt x n) 0)))

(defthm neg-bitn_alt-1
    (implies (and (integerp x)
                  (integerp n)
                  (< x 0)
		  (>= x (- (expt 2 n))))
	     (equal (bitn_alt x n) 1)))

(defthmd bitn_alt-shift
  (implies (and (integerp n)
		(integerp k))
	   (equal (bitn_alt (* x (expt 2 k)) (+ n k))
		  (bitn_alt x n))))

(defthmd bitn_alt-shift-down
  (implies (and (natp i)
		(integerp k))
	   (equal (bitn_alt (fl (/ x (expt 2 k))) i)
		  (bitn_alt x (+ i k)))))

(defthm bitn_alt-bits_alt
  (implies (and (<= k (- i j))
		(case-split (<= 0 k))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k)))
	   (equal (bitn_alt (bits_alt x i j) k)
		  (bitn_alt x (+ j k)))))

(defthmd bitn_alt-plus-bits_alt
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits_alt x n m)
		(+ (* (bitn_alt x n) (expt 2 (- n m)))
		   (bits_alt x (1- n) m)))))

(defthm bits_alt-plus-bitn_alt
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits_alt x n m)
		(+ (bitn_alt x m)
		   (* 2 (bits_alt x n (1+ m))))))
  :rule-classes ())

(defun sumbits_alt (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn_alt x (1- n)))
       (sumbits_alt x (1- n)))))

(defthmd sumbits_alt-bits_alt
    (implies (and (integerp x)
		  (natp n)
		  (> n 0))
	     (equal (sumbits_alt x n)
		    (bits_alt x (1- n) 0))))

(defthmd sumbits_alt-thm
    (implies (and (bvecp x n)
		  (natp n)
		  (> n 0))
	     (equal (sumbits_alt x n)
		    x)))

; The lemmas sumbits_alt-badguy-is-correct and sumbits_alt-badguy-bounds, below, let
; one prove equality of two bit vectors of width k by proving each of these has
; the same value at bit i, for arbitrary i from 0 to k-1.

(defun sumbits_alt-badguy (x y k)
  (if (zp k)
      0
    (if (not (equal (bitn_alt x (1- k)) (bitn_alt y (1- k))))
        (1- k)
      (sumbits_alt-badguy x y (1- k)))))

(defthmd sumbits_alt-badguy-is-correct
  (implies (and (bvecp x k)
                (bvecp y k)
                (equal (bitn_alt x (sumbits_alt-badguy x y k))
                       (bitn_alt y (sumbits_alt-badguy x y k)))
                (integerp k)
                (< 0 k))
           (equal (equal x y) t)))

(defthmd sumbits_alt-badguy-bounds
  (implies (and (integerp k)
                (< 0 k))
           (let ((badguy (sumbits_alt-badguy x y k)))
             (and (integerp badguy)
                  (<= 0 badguy)
                  (< badguy k)))))

(defun all-bits-p (b k)
  (if (zp k)
      t
    (and (or (= (nth (1- k) b) 0)
	     (= (nth (1- k) b) 1))
	 (all-bits-p b (1- k)))))

(defun sum-b (b k)
  (if (zp k)
      0
    (+ (* (expt 2 (1- k)) (nth (1- k) b))
       (sum-b b (1- k)))))

(defthmd sum-bitn_alt
  (implies (and (natp n)
		(all-bits-p b n)
	        (natp k)
		(< k n))
           (equal (bitn_alt (sum-b b n) k)
	          (nth k b))))

(defthmd bvecp-bitn_alt-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
		  (natp n))
	     (equal (bitn_alt x n) 1)))

(defthmd bvecp-bitn_alt-2
  (implies (and (bvecp x n)
		(< k n)
		(<= (- (expt 2 n) (expt 2 k)) x)
		(integerp n)
		(integerp k))
	   (equal (bitn_alt x k) 1))
  :rule-classes ((:rewrite :match-free :all)))

(defthm neg-bitn_alt-0
    (implies (and (integerp x)
		  (natp n)
		  (< x (- (expt 2 n)))
		  (>= x (- (expt 2 (1+ n)))))
	     (equal (bitn_alt x n) 0)))

(defthm neg-bitn_alt-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (< k n)
		  (< x (- (expt 2 k) (expt 2 n)))
		  (>= x (- (expt 2 n))))
	     (equal (bitn_alt x k) 0)))

(defthmd bitn_alt-expt
    (implies (case-split (integerp n))
	     (equal (bitn_alt (expt 2 n) n)
		    1)))

(defthmd bitn_alt-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn_alt (expt 2 i) n)
		  0)))

(defthm bitn_alt-plus-expt-1
    (implies (and (rationalp x)
		  (integerp n))
	     (not (equal (bitn_alt (+ x (expt 2 n)) n)
			 (bitn_alt x n))))
  :rule-classes ())

(defthmd bitn_alt-plus-mult
    (implies (and (< n m)
		  (integerp m)
		  (integerp k))
	     (equal (bitn_alt (+ x (* k (expt 2 m))) n)
		    (bitn_alt x n))))

(defthmd bitn_alt-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt 2 (1+ n))) 0))
	     (equal (bitn_alt (+ c x) n)
		    (bitn_alt x n))))


;;;**********************************************************************
;;;			     CAT
;;;**********************************************************************

(defund binary-cat_alt (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits_alt x (1- m) 0))
         (bits_alt y (1- n) 0))
    0))

;;Definition of the macro, cat_alt:

;;X is a list of alternating data values and sizes.  CAT_ALT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat_alt (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits_alt ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat_alt ,@x))
        (t
         `(binary-cat_alt ,(car x)
                      ,(cadr x)
                      (cat_alt ,@(cddr x))
                      ,(cat-size (cddr x))))))

(defthm cat_alt-nonnegative-integer-type
  (and (integerp (cat_alt x m y n))
       (<= 0 (cat_alt x m y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-cat_alt)))

(defthm cat_alt-bvecp
  (implies (and (<= (+ m n) k)
		(case-split (integerp k)))
	   (bvecp (cat_alt x m y n) k)))

(defthm cat_alt-with-n-0
  (equal (binary-cat_alt x m y 0)
	 (bits_alt x (1- m) 0)))

(defthm cat_alt-with-m-0
  (equal (binary-cat_alt x 0 y n)
	 (bits_alt y (1- n) 0)))

(defthm cat_alt-0
  (implies (and (case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (cat_alt 0 m y n) y)))

(defthmd cat_alt-bits_alt-1
    (equal (cat_alt (bits_alt x (1- m) 0) m y n)
	   (cat_alt x m y n)))

(defthmd cat_alt-bits_alt-2
    (equal (cat_alt x m (bits_alt y (1- n) 0) n)
	   (cat_alt x m y n)))

(defthm cat_alt-associative
  (implies (and (case-split (<= (+ m n) p))
		(case-split (<= 0 m))
		(case-split (<= 0 n))
		(case-split (<= 0 q))
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp p))
		(case-split (integerp q)))
	   (equal (cat_alt (cat_alt x m y n) p z q)
		  (cat_alt x m (cat_alt y n z q) (+ n q)))))

(defthmd cat_alt-equal-constant
  (implies (and (syntaxp (and (quotep k)
			      (quotep m)
			      (quotep n)))
		(case-split (bvecp y n))
		(case-split (bvecp x m))
		(case-split (< k (expt 2 (+ m n)))) ;not a problem hyp, since k, m and n are constants
		(case-split (integerp k))
		(case-split (<= 0 k))
		(case-split (integerp m))
		(case-split (<= 0 m))
		(case-split (integerp n))
		(case-split (<= 0 n)))
	   (equal (equal k (cat_alt x m y n))
		  (and (equal y (bits_alt k (1- n) 0))
		       (equal x (bits_alt k (+ -1 m n) n))))))

(defthmd cat_alt-equal-rewrite
  (implies (and (case-split (bvecp x1 m))
		(case-split (bvecp y1 n))
		(case-split (bvecp x2 m))
		(case-split (bvecp y2 n))
		(case-split (integerp n))
		(case-split (<= 0 n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (equal (cat_alt x1 m y1 n)
			 (cat_alt x2 m y2 n))
		  (and (equal x1 x2)
		       (equal y1 y2)))))

(defthm cat_alt-bits_alt-bits_alt
  (implies (and (equal j (1+ k))
		(equal n (+ 1 (- l) k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (<= l k))
		(case-split (integerp i))
		(case-split (integerp k))
		(case-split (integerp l))
		(case-split (integerp m)))
	   (equal (cat_alt (bits_alt x i j) m (bits_alt x k l) n)
		  (bits_alt x i l))))

(defthm cat_alt-bitn_alt-bits_alt
    (implies (and (equal j (1+ k))
		  (equal n (+ 1 (- l) k))
		  (case-split (<= 1 m))
		  (case-split (<= l k))
		  (case-split (integerp j))
		  (case-split (integerp k))
		  (case-split (integerp l))
		  (case-split (integerp m)))
	     (equal (cat_alt (bitn_alt x j) m (bits_alt x k l) n)
		    (bits_alt x j l))))

(defthm cat_alt-bits_alt-bitn_alt
  (implies (and (equal j (1+ k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp m)))
	   (equal (cat_alt (bits_alt x i j) m (bitn_alt x k) 1)
		  (bits_alt x i k))))

(defthm cat_alt-bitn_alt-bitn_alt
  (implies (and (equal i (1+ j))
		(case-split (integerp i))
		(case-split (integerp j)))
	   (equal (cat_alt (bitn_alt x i) 1 (bitn_alt x j) 1)
		  (bits_alt x i j))))

(defthmd bits_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i))
		(case-split (natp j)))
	   (equal (bits_alt (cat_alt x m y n) i j)
		  (if (< i n)
		      (bits_alt y i j)
		    (if (>= j n)
			(bits_alt x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat_alt (bits_alt x (if (< i (+ m n))
					(- i n)
				      (1- m)) 0)
			    (1+ (- i n))
			    (bits_alt y (1- n) j)
			    (- n j)))))))

(defthm bits_alt-cat_alt-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(syntaxp (quotep j))
		(natp n)
		(natp m)
		(natp i)
		(natp j))
	   (equal (bits_alt (cat_alt x m y n) i j)
		  (if (< i n)
		      (bits_alt y i j)
		    (if (>= j n)
			(bits_alt x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat_alt (bits_alt x (if (< i (+ m n))
				       (- i n)
				     (1- m)) 0)
			   (1+ (- i n))
			   (bits_alt y (1- n) j)
			   (- n j)))))))

(defthmd bitn_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i)))
	   (equal (bitn_alt (cat_alt x m y n) i)
		  (if (< i n)
		      (bitn_alt y i)
		    (if (< i (+ m n))
		      (bitn_alt x (- i n))
		    0)))))

(defthm bitn_alt-cat_alt-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(natp n)
		(natp m)
		(natp i))
	   (equal (bitn_alt (cat_alt x m y n) i)
		  (if (< i n)
		      (bitn_alt y i)
		    (if (< i (+ m n))
		      (bitn_alt x (- i n))
		    0)))))

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat_alt, which can't
; be changed because of the guard of bits_alt.
(defund mulcat_alt (l n x)
  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat_alt (mulcat_alt l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits_alt x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat_alt (mulcat_alt l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

(defthm mulcat_alt-nonnegative-integer-type
  (and (integerp (mulcat_alt l n x))
       (<= 0 (mulcat_alt l n x)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription mulcat_alt)))

(defthmd mulcat_alt-bits_alt
    (implies (and (integerp l)
		  (integerp x))
	     (equal (mulcat_alt l n (bits_alt x (1- l) 0))
		    (mulcat_alt l n x))))

(defthm mulcat_alt-bvecp
  (implies (and (>= p (* l n))
		(case-split (integerp p))
		(case-split (natp l)))
	   (bvecp (mulcat_alt l n x) p)))

(defthm mulcat_alt-1
    (implies (natp l)
	     (equal (mulcat_alt l 1 x)
		    (bits_alt x (1- l) 0))))

(defthm mulcat_alt-0
  (equal (mulcat_alt l n 0) 0))

(defthm mulcat_alt-n-1
  (implies (case-split (<= 0 n))
	   (equal (mulcat_alt 1 n 1)
		  (1- (expt 2 n)))))

(defthm bitn_alt-mulcat_alt-1
  (implies (and (< m n)
		(case-split (bvecp x 1))
		(case-split (natp m))
		(case-split (integerp n)))
	   (equal (bitn_alt (mulcat_alt 1 n x) m)
		  x)))

;;;;;
;;;;;

(defthmd bits_alt-bits_alt-times
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i))
	     (equal (bits_alt (* (bits_alt x i 0) y) i 0)
                    (bits_alt (* x y) i 0))))
