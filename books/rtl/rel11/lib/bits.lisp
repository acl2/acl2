; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   1106 W 9th St., Austin, TX 78703
;   david@russinoff.com
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")

;;;**********************************************************************
;;;				BVECP
;;;**********************************************************************

(defsection-rtl |Recognizing Bit Vectors| |Bit Vectors|

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

(defun nats (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) () (cons (1- n) (nats (1- n)))))

(defthm bvecp-member
  (implies (and (natp n)
                (bvecp x n))
           (member x (nats (expt 2 n))))
  :rule-classes ())

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
)

;;;**********************************************************************
;;;			    BITS
;;;**********************************************************************

(defsection-rtl |Bit Slices| |Bit Vectors|

(defund bits (x i j)
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

(defthm bits-nonnegative-integerp-type
  (and (<= 0 (bits x i j))
       (integerp (bits x i j)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription bits)))

(defthm bits-bvecp
    (implies (and (<= (+ 1 i (- j)) k)
		  (case-split (integerp k)))
	     (bvecp (bits x i j) k)))

;;Here is a variation of bits-bvecp that is less general but does not
;;require an integerp hypothesis:

(defthm bits-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits x i j) k)))

(defthm bits-bounds
    (implies (and (integerp i)
		  (integerp j))
	     (and (natp (bits x i j))
		  (< (bits x i j) (expt 2 (1+ (- i j))))))
  :rule-classes())

(defthm mod-bits-equal
  (implies (= (mod x (expt 2 (1+ i)))
	      (mod y (expt 2 (1+ i))))
	   (= (bits x i j) (bits y i j)))
  :rule-classes ())

(defthmd mod-bits-equal-cor
    (implies (and (integerp x)
		  (integerp n)
		  (integerp i)
		  (integerp j)
		  (< i n))
	     (equal (bits (mod x (expt 2 n)) i j)
		    (bits x i j))))

(defthmd bits-mod
  (implies (and (case-split (integerp x))
		(case-split (integerp i)))
	   (equal (bits x i 0)
		  (mod x (expt 2 (1+ i))))))

(defthm bits-diff-equal
    (implies (and (natp n)
		  (integerp x)
		  (integerp y)
		  (< (abs (- x y)) (expt 2 n)))
	     (iff (= x y)
		  (= (bits (- x y) (1- n) 0) 0)))
  :rule-classes ())

(defthm bits-tail
  (implies (and (bvecp x (1+ i))
		(case-split (acl2-numberp i)))
	   (equal (bits x i 0) x)))

(defthm bits-tail-gen
    (implies (and (integerp x)
		  (natp i)
		  (< x (expt 2 i))
		  (>= x (- (expt 2 (+ 1 i)))))
	     (equal (bits x i 0)
		    (if (>= x 0)
			x
		      (+ x (expt 2 (+ 1 i)))))))

(defthmd neg-bits-1
    (implies (and (integerp x)
		  (natp i)
		  (natp j)
		  (< x 0)
		  (>= x (- (expt 2 j)))
		  (>= i j))
	     (equal (bits x i j)
                    (1- (expt 2 (1+ (- i j)))))))

(defthmd bits-top-ones
  (implies (and (natp i)
                (natp j)
		(>= i j)
		(natp x)
		(< x (expt 2 (1+ i)))
		(>= x (- (expt 2 (1+ i)) (expt 2 j))))
	   (equal (bits x i j)
	          (1- (expt 2 (- (1+ i) j))))))

(defthm bits-bits-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (+ (bits x k 0) y) i j)
		  (bits (+ x y) i j))))

(defthm bits-bits-sum-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (+ x (bits y k 0)) i j)
		  (bits (+ x y) i j))))

(defthmd bits-bits-diff
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (+ x (- (bits y k 0))) i j)
		  (bits (- x y) i j))))

(defthmd bits-bits-prod
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (* x (bits y k 0)) i j)
		  (bits (* x y) i j))))


(defthm bits-fl-diff
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits x (1- i) j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- i j))
                        (fl (/ x (expt 2 i)))))))
  :rule-classes ())

(defthm bits-mod-fl
  (implies (and (integerp i)
                (integerp j))
           (equal (bits x (1- i) j)
                  (mod (fl (/ x (expt 2 j)))
                       (expt 2 (- i j)))))
  :rule-classes ())

(defthm bits-neg-indices
  (implies (and (< i 0)
                (integerp x))
           (equal (bits x i j) 0)))

(defthm bits-reverse-indices
  (implies (< i j)
	   (equal (bits x i j)
		  0)))

(defthmd bvecp-bits-0
  (implies (bvecp x j)
	   (equal (bits x i j) 0)))

(defthm bits-0
  (equal (bits 0 i j) 0))

(defthmd bits-shift-down-1
  (implies (and (<= 0 j)
		(integerp i)
		(integerp j)
		(integerp k))
	   (equal (bits (fl (/ x (expt 2 k))) i j)
		  (bits x (+ i k) (+ j k)))))

(defthmd bits-shift-down-2
  (implies (and (integerp x)
		(natp i)
		(natp k))
	   (equal (fl (/ (bits x (+ i k) 0) (expt 2 k)))
		  (bits (fl (/ x (expt 2 k))) i 0))))

(defthmd bits-shift-up-1
  (implies (and (integerp k)
		(integerp i)
		(integerp j))
	   (equal (bits (* (expt 2 k) x) i j)
		  (bits x (- i k) (- j k)))))

(defthmd bits-shift-up-2
  (implies (and (integerp x)
		(natp k)
		(integerp i))
	   (equal (* (expt 2 k) (bits x i 0))
		  (bits (* (expt 2 k) x) (+ i k) 0))))

(defthmd bits-plus-mult-1
  (implies (and (bvecp x k)
		(<= k m)
		(integerp y)
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp k)))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits y (- n k) (- m k)))))

(defthmd bits-plus-mult-2
  (implies (and (< n k)
		(integerp y)
		(integerp k))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits x n m))))

(defthmd bits-plus-mult-2-rewrite
   (implies (and (syntaxp (quotep c))
                 (equal (mod c (expt 2 (1+ n))) 0))
            (equal (bits (+ c x) n m)
                   (bits x n m))))

(defthm bits-plus-bits
    (implies (and (integerp m)
		  (integerp p)
		  (integerp n)
		  (<= m p)
		  (<= p n))
	     (= (bits x n m)
		(+ (bits x (1- p) m)
		   (* (expt 2 (- p m)) (bits x n p)))))
  :rule-classes ())

(defthm bits-bits
  (implies (and (case-split (<= 0 l))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp l)))
	   (equal (bits (bits x i j) k l)
		  (if (<= k (- i j))
		      (bits x (+ k j) (+ l j))
		    (bits x i (+ l j))))))

;;bits-match can prove things like this:
;;(thm (implies (equal 12 (bits x 15 6))
;;		(equal 4 (bits x 8 6))))

(defthmd bits-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free variables
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(equal k (bits k2 (+ i (- j2)) (+ (- j2) j)))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j) (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  t)))

;;bits-dont-match can prove things like this:
;;(thm (implies (equal 7 (bits x 8 6))
;;		(not (equal 4 (bits x 15 6)))))

(defthmd bits-dont-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(not (equal k (bits k2 (+ i (- j2)) (+ (- j2) j))))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j) (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  nil)))
)

;;;**********************************************************************
;;;				BITN
;;;**********************************************************************

(defsection-rtl |Bit Extraction| |Bit Vectors|

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defthm bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription bitn)))

(defthm bits-n-n-rewrite
  (equal (bits x n n)
	 (bitn x n)))

(defthmd bitn-def
  (implies (case-split (integerp n))
	   (equal (bitn x n)
		  (mod (fl (/ x (expt 2 n))) 2))))

;;A recursive formulation:

(defthmd bitn-rec-0
  (implies (integerp x)
	   (equal (bitn x 0) (mod x 2))))

(defthmd bitn-rec-pos
    (implies (< 0 n)
	     (equal (bitn x n)
		    (bitn (fl (/ x 2)) (1- n))))
  :rule-classes ((:definition :controller-alist ((bitn t t)))))

;;Use this to induce case-splitting:

(defthm bitn-0-1
    (or (equal (bitn x n) 0)
	(equal (bitn x n) 1))
  :rule-classes ())

(defthm bitn-bvecp
  (implies (and (<= 1 k)
		(case-split (integerp k)))
	   (bvecp (bitn x n) k)))

;;The following is a special case of bitn-bvecp.
;;It is useful as a :forward-chaining rule in concert with bvecp-0-1 and
;;bvecp-1-0.

(defthm bitn-bvecp-forward
  (bvecp (bitn x n) 1)
  :rule-classes ((:forward-chaining :trigger-terms ((bitn x n)))))

(defthm bitn-neg
  (implies (and (< n 0)
                (integerp x))
           (equal (bitn x n) 0)))

(defthm bitn-0
  (equal (bitn 0 k) 0))

(defthm bitn-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn x 0) x)))

(defthm bitn-bitn-0
    (equal (bitn (bitn x n) 0)
	   (bitn x n)))

(defthmd bitn-mod
    (implies (and (< k n)
		  (integerp n)
		  (integerp k))
	     (equal (bitn (mod x (expt 2 n)) k)
		    (bitn x k))))

(defthm bvecp-bitn-0
    (implies (bvecp x n)
	     (equal (bitn x n) 0)))

(defthm neg-bitn-1
    (implies (and (integerp x)
                  (integerp n)
                  (< x 0)
		  (>= x (- (expt 2 n))))
	     (equal (bitn x n) 1)))

(defthmd bitn-minus-1
    (implies (natp i)
	     (equal (bitn -1 i) 1)))

;; The rewrite rule neg-bitn-2 has the hypotheses (integerp n) and (< x (- (expt 2 k) (expt 2 n))),
;; where n does not occur in the lhs.  When n is bound to a large integer, (expt 2 n) blows up.

(defthmd neg-bitn-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (< k n)
		  (< x (- (expt 2 k) (expt 2 n)))
		  (>= x (- (expt 2 n))))
	     (equal (bitn x k) 0)))

(defthm neg-bitn-0
    (implies (and (integerp x)
		  (natp n)
		  (< x (- (expt 2 n)))
		  (>= x (- (expt 2 (1+ n)))))
	     (equal (bitn x n) 0)))

(defthmd bitn-shift-up
  (implies (and (integerp n)
		(integerp k))
	   (equal (bitn (* x (expt 2 k)) (+ n k))
		  (bitn x n))))

(defthmd bitn-shift-down
  (implies (and (natp i)
		(integerp k))
	   (equal (bitn (fl (/ x (expt 2 k))) i)
		  (bitn x (+ i k)))))

(defthmd bitn-bits
  (implies (and (<= k (- i j))
		(case-split (<= 0 k))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k)))
	   (equal (bitn (bits x i j) k)
		  (bitn x (+ j k)))))

(defthm bitn-plus-bits
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :rule-classes ())

(defthm bits-plus-bitn
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ())

(defun sumbits (x n)
  (declare (xargs :guard (and (integerp x)
                              (natp n))))
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))

(defthmd sumbits-bits
    (implies (and (integerp x)
		  (natp n)
		  (> n 0))
	     (equal (sumbits x n)
		    (bits x (1- n) 0))))

(defthmd sumbits-thm
    (implies (and (bvecp x n)
		  (natp n)
		  (> n 0))
	     (equal (sumbits x n)
		    x)))

(defnd all-bits-p (b k)
  (if (posp k)
      (and (consp b)
           (all-bits-p (cdr b) (1- k))
           (or (equal (car b) 0)
               (equal (car b) 1)))
    (and (true-listp b)
         (equal k 0))))

(defun sum-b (b k)
  (declare (xargs :guard (all-bits-p b k)))
  (if (zp k)
      0
    (+ (* (expt 2 (1- k)) (nth (1- k) b))
       (sum-b b (1- k)))))

(defthmd sum-bitn
  (implies (and (all-bits-p b n)
	        (natp k)
		(< k n))
           (equal (bitn (sum-b b n) k)
	          (nth k b))))

;; The next lemma can be used to prove equality of two bit vectors by
;; proving that they have the same value at bit n for all n.

(defn bit-diff (x y)
  (declare (xargs :measure (:? x y)))
  (if (or (not (integerp x))
          (not (integerp y))
          (= x y))
      ()
    (if (= (bitn x 0) (bitn y 0))
        (1+ (bit-diff (fl (/ x 2)) (fl (/ y 2))))
      0)))

(defthm bit-diff-diff
  (implies (and (integerp x)
                (integerp y)
                (not (= x y)))
           (let ((n (bit-diff x y)))
             (and (natp n)
                  (not (= (bitn x n) (bitn y n))))))
  :rule-classes ())

(defthmd bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
		  (natp n))
	     (equal (bitn x n) 1)))

(defthmd bvecp-bitn-2
  (implies (and (bvecp x n)
		(< k n)
		(<= (- (expt 2 n) (expt 2 k)) x)
		(integerp n)
		(integerp k))
	   (equal (bitn x k) 1))
  :rule-classes ((:rewrite :match-free :all)))

(defthmd bitn-expt
    (implies (case-split (integerp n))
	     (equal (bitn (expt 2 n) n)
		    1)))

(defthmd bitn-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn (expt 2 i) n)
		  0)))

(defthm bitn-plus-expt-1
    (implies (and (rationalp x)
		  (integerp n))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ())

(defthmd bitn-plus-mult
    (implies (and (< n m)
		  (integerp m)
		  (integerp k))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n))))

(defthmd bitn-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt 2 (1+ n))) 0))
	     (equal (bitn (+ c x) n)
		    (bitn x n))))
)

;;;**********************************************************************
;;;			     CAT
;;;**********************************************************************

(defsection-rtl |Concatenation| |Bit Vectors|

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

;; We define a macro, CAT, that takes a list of alternating data values and
;; sizes.  CAT-SIZE returns the formal sum of the sizes.  The list must contain
;; at least 1 data/size pair, but we do not need to specify this in the guard,
;; and leaving it out of the guard simplifies the guard proof.

(defn formal-+ (x y)
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x)
                              (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

(defthm cat-nonnegative-integer-type
  (and (integerp (cat x m y n))
       (<= 0 (cat x m y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-cat)))

(defthm cat-bvecp
  (implies (and (<= (+ m n) k)
		(case-split (integerp k)))
	   (bvecp (cat x m y n) k)))

(defthm cat-with-n-0
  (equal (binary-cat x m y 0)
	 (bits x (1- m) 0)))

(defthm cat-with-m-0
  (equal (binary-cat x 0 y n)
	 (bits y (1- n) 0)))

(defthmd cat-0
  (implies (and (case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (cat 0 m y n) y)))

(defthmd cat-bits-1
    (equal (cat (bits x (1- m) 0) m y n)
	   (cat x m y n)))

(defthmd cat-bits-2
    (equal (cat x m (bits y (1- n) 0) n)
	   (cat x m y n)))

(defthm cat-bits-3
  (implies (and (integerp i) (integerp m) (>= i (1- m)))
           (equal (cat (bits x i 0) m y n)
                  (cat x m y n))))

(defthm cat-bits-4
  (implies (and (integerp i) (integerp n) (>= i (1- n)))
           (equal (cat x m (bits y i 0) n)
                  (cat x m y n))))

(defthm cat-associative
  (implies (and (case-split (<= (+ m n) p))
		(case-split (<= 0 m))
		(case-split (<= 0 n))
		(case-split (<= 0 q))
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp p))
		(case-split (integerp q)))
	   (equal (cat (cat x m y n) p z q)
		  (cat x m (cat y n z q) (+ n q)))))

(defthmd cat-equal-constant
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
	   (equal (equal k (cat x m y n))
		  (and (equal y (bits k (1- n) 0))
		       (equal x (bits k (+ -1 m n) n))))))

(defthmd cat-equal-rewrite
  (implies (and (case-split (bvecp x1 m))
		(case-split (bvecp y1 n))
		(case-split (bvecp x2 m))
		(case-split (bvecp y2 n))
		(case-split (integerp n))
		(case-split (<= 0 n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (equal (cat x1 m y1 n)
			 (cat x2 m y2 n))
		  (and (equal x1 x2)
		       (equal y1 y2)))))

(defthm cat-bits-bits
  (implies (and (equal j (1+ k))
		(equal n (+ 1 (- l) k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (<= l k))
		(case-split (integerp i))
		(case-split (integerp k))
		(case-split (integerp l))
		(case-split (integerp m)))
	   (equal (cat (bits x i j) m (bits x k l) n)
		  (bits x i l))))

(defthm cat-bitn-bits
    (implies (and (equal j (1+ k))
		  (equal n (+ 1 (- l) k))
		  (case-split (<= 1 m))
		  (case-split (<= l k))
		  (case-split (integerp j))
		  (case-split (integerp k))
		  (case-split (integerp l))
		  (case-split (integerp m)))
	     (equal (cat (bitn x j) m (bits x k l) n)
		    (bits x j l))))

(defthm cat-bits-bitn
  (implies (and (equal j (1+ k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp m)))
	   (equal (cat (bits x i j) m (bitn x k) 1)
		  (bits x i k))))

(defthm cat-bitn-bitn
  (implies (and (equal i (1+ j))
		(case-split (integerp i))
		(case-split (integerp j)))
	   (equal (cat (bitn x i) 1 (bitn x j) 1)
		  (bits x i j))))

(defthmd bits-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i))
		(case-split (natp j)))
	   (equal (bits (cat x m y n) i j)
		  (if (< i n)
		      (bits y i j)
		    (if (>= j n)
			(bits x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat (bits x (if (< i (+ m n))
					(- i n)
				      (1- m)) 0)
			    (1+ (- i n))
			    (bits y (1- n) j)
			    (- n j)))))))

(defthm bits-cat-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(syntaxp (quotep j))
		(natp n)
		(natp m)
		(natp i)
		(natp j))
	   (equal (bits (cat x m y n) i j)
		  (if (< i n)
		      (bits y i j)
		    (if (>= j n)
			(bits x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat (bits x (if (< i (+ m n))
				       (- i n)
				     (1- m)) 0)
			   (1+ (- i n))
			   (bits y (1- n) j)
			   (- n j)))))))

(defthmd bitn-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i)))
	   (equal (bitn (cat x m y n) i)
		  (if (< i n)
		      (bitn y i)
		    (if (< i (+ m n))
		      (bitn x (- i n))
		    0)))))

(defthm bitn-cat-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(natp n)
		(natp m)
		(natp i))
	   (equal (bitn (cat x m y n) i)
		  (if (< i n)
		      (bitn y i)
		    (if (< i (+ m n))
		      (bitn x (- i n))
		    0)))))

(defund mulcat (l n x)
  (declare (xargs :guard (and (natp l)
                              (natp n)
                              (natp x))))
  (if (and (integerp n) (> n 0))
      (cat (mulcat l (1- n) x)
           (* l (1- n))
           x
           l)
    0))

(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription mulcat)))

(defthmd mulcat-bits
    (implies (and (integerp l)
		  (integerp x))
	     (equal (mulcat l n (bits x (1- l) 0))
		    (mulcat l n x))))

(defthm mulcat-bvecp
  (implies (and (>= p (* l n))
		(case-split (integerp p))
		(case-split (natp l)))
	   (bvecp (mulcat l n x) p)))

(defthm mulcat-1
    (implies (natp l)
	     (equal (mulcat l 1 x)
		    (bits x (1- l) 0))))

(defthm mulcat-0
  (equal (mulcat l n 0) 0))

(defthm mulcat-n-1
  (implies (case-split (<= 0 n))
	   (equal (mulcat 1 n 1)
		  (1- (expt 2 n)))))

(defthm bitn-mulcat-1
  (implies (and (< m n)
		(case-split (bvecp x 1))
		(case-split (natp m))
		(case-split (integerp n)))
	   (equal (bitn (mulcat 1 n x) m)
		  x)))
)

;;;**********************************************************************
;;;		 Signed Integer and Fixed-Point Encodings
;;;**********************************************************************

(defsection-rtl |Signed Integer Formats| |Bit Vectors|

(defnd ui (r) r)

(defund si (r n)
  (declare (xargs :guard (and (integerp r)
                              (natp n))))
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defthm int-si
  (implies (and (integerp r)
                (natp n))
	   (integerp (si r n)))
  :rule-classes (:type-prescription :rewrite))

(defthm si-bits
    (implies (and (integerp x)
		  (natp n)
		  (< x (expt 2 (1- n)))
		  (>= x (- (expt 2 (1- n)))))
	     (= (si (bits x (1- n) 0) n)
                x))
    :rule-classes ())

(defthmd bits-si
  (implies (and (integerp n)
                (< i n))
           (equal (bits (si r n) i j)
                  (bits r i j))))

(defthmd si-shift
  (implies (and (natp n)
                (natp k)
                (bvecp r n))
           (equal (si (* (expt 2 k) r) (+ k n))
                  (* (expt 2 k) (si r n)))))

(defund sextend (m n r)
  (declare (xargs :guard (and (natp m)
                              (natp n)
                              (integerp r))))
  (bits (si r n) (1- m) 0))

(defthmd si-sextend
    (implies (and (natp n)
		  (natp m)
		  (<= n m)
		  (bvecp r n))
	     (equal (si (sextend m n r) m)
		    (si r n))))

(defthmd si-approx
  (implies (and (not (zp n))
                (integerp x)
                (integerp y)
                (< (abs (si (mod x (expt 2 n)) n))
                   (- (expt 2 (1- n)) (abs (- x y)))))
           (equal (- (si (mod x (expt 2 n)) n)
                     (si (mod y (expt 2 n)) n))
                  (- x y))))


;;;**********************************************************************
;;;                      Fixed-Point Registers
;;;**********************************************************************

(defund uf (r n m)
  (declare (xargs :guard (and (natp r)
                              (natp n)
                              (natp m))))
  (* (expt 2 (- m n)) (ui r)))

(defund sf (r n m)
  (declare (xargs :guard (and (integerp r)
                              (natp n)
                              (natp m))))
  (* (expt 2 (- m n)) (si r n)))

(defthmd bits-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i)))))))))

(defthmd bits-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i)
                  (< i n))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i)))))))))

(defthm chop-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (integerp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :rule-classes ())

(defthm chop-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (integerp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :rule-classes ())

(defthmd sf-val
  (implies (and (natp n)
                (natp m)
                (<= m n)
                (bvecp r n)
                (integerp y)
                (= (mod y (expt 2 n)) r)
                (<= (- (expt 2 (1- n))) y)
                (< y (expt 2 (1- n))))
            (equal (sf r n m)
                   (* (expt 2 (- m n)) y))))
)
