(in-package "ACL2")

(set-enforce-redundancy t)

(include-book "basic")

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;;;**********************************************************************
;;;				BVECP
;;;**********************************************************************

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

(defthm bvecp-product
    (implies (and (bvecp x m)
		  (bvecp y n))
	     (bvecp (* x y) (+ m n)))
  :rule-classes ())

(defthmd bvecp-monotone
    (implies (and (bvecp x n)
		  (<= n m)
		  (case-split (integerp m)))
	     (bvecp x m)))

(defthmd bvecp-shift-down
    (implies (and (bvecp x n)
		  (natp n)
		  (natp k)
		  (>= n k))
	     (bvecp (fl (/ x (expt 2 k))) (- n k))))

(defthmd bvecp-shift-up
    (implies (and (bvecp x (- n m))
		  (natp m)
		  (integerp n))
	     (bvecp (* x (expt 2 m)) n)))

(defthm bvecp-1-0
  (implies (and (bvecp x 1)
		(not (equal x 1)))
	   (equal x 0))
  :rule-classes :forward-chaining)

;;The following is a contrapositive of bvecp-1-0.  It could be given as a
;;corollary.
(defthm bvecp-0-1
  (implies (and (bvecp x 1)
		(not (equal x 0)))
	   (equal x 1))
  :rule-classes :forward-chaining)

;;This lemma may be enabled to induce case-splitting on bit vectors of
;;length 1:

(defthmd bvecp-1-rewrite
  (equal (bvecp x 1)
	 (or (equal x 0) (equal x 1))))

(defun bitvec (x n)
  (if (bvecp x n) x 0))

;;;**********************************************************************
;;;				BITN
;;;**********************************************************************

(defthmd bitn-def
  (implies (case-split (integerp k))
	   (equal (bitn x k)
		  (mod (fl (/ x (expt 2 k))) 2))))

(defthm bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :rule-classes (:type-prescription))

;;(:type-prescription bitn) is no better than bitn-nonnegative-integer-type
;;and might be worse:

(in-theory (disable (:type-prescription bitn)))

;;A recursive formulation:

(defthmd bitn-rec-0
  (implies (integerp x)
	   (equal (bitn x 0) (mod x 2))))

(defthmd bitn-rec-pos
    (implies (< 0 k)
	     (equal (bitn x k)
		    (bitn (fl (/ x 2)) (1- k))))
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

(defthm bitn-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn x 0) x)))

(defthm bitn-bitn-0
    (equal (bitn (bitn x n) 0)
	   (bitn x n)))

(defthm bitn-0
  (equal (bitn 0 k) 0))

(defthmd bitn-mod
    (implies (and (< k n)
		  (integerp n)
		  (integerp k))
	     (equal (bitn (mod x (expt 2 n)) k)
		    (bitn x k))))

(defthm bvecp-bitn-0
    (implies (bvecp x n)
	     (equal (bitn x n) 0)))

(defthmd bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
		  (natp n))
	     (equal (bitn x n) 1)))

;n is a free var
(defthmd bvecp-bitn-2
  (implies (and (bvecp x n)
		(< k n)
		(<= (- (expt 2 n) (expt 2 k)) x)
		(integerp n)
		(integerp k))
	   (equal (bitn x k) 1))
  :rule-classes ((:rewrite :match-free :all)))

(defthmd bitn-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn (expt 2 i) n)
		  0)))

(defthmd bitn-expt
    (implies (case-split (integerp n))
	     (equal (bitn (expt 2 n) n)
		    1)))

(defthm bitn-plus-expt-1
    (implies (and (rationalp x)
		  (integerp n))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ())

(defthmd bitn-plus-expt-2
    (implies (and (< n m)
		  (integerp n)
		  (integerp m))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (bitn x n))))

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

(defthmd bitn-shift
  (implies (and (integerp n)
		(integerp k))
	   (equal (bitn (* x (expt 2 k)) (+ n k))
		  (bitn x n))))


;;;**********************************************************************
;;;			    BITS
;;;**********************************************************************

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))))
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

;;(:type-prescription bits) is no better than bits-nonnegative-integer-type
;;and might be worse:

(in-theory (disable (:type-prescription bits)))

(defthmd bits-mod
  (implies (and (case-split (integerp x))
		(case-split (integerp i)))
	   (equal (bits x i 0)
		  (mod x (expt 2 (1+ i))))))

(defthm mod-bits-equal
  (implies (= (mod x (expt 2 (1+ i)))
	      (mod y (expt 2 (1+ i))))
	   (= (bits x i j) (bits y i j)))
  :rule-classes ())

(defthm bits-0
  (equal (bits 0 i j) 0))

(defthm bits-with-indices-in-the-wrong-order
  (implies (< i j)
	   (equal (bits x i j)
		  0)))

(defthm bits-n-n-rewrite
  (equal (bits x n n)
	 (bitn x n)))

(defthmd bvecp-bits-0
  (implies (bvecp x j)
	   (equal (bits x i j) 0)))

(defthm bits-tail
  (implies (and (bvecp x (1+ i))
		(case-split (acl2-numberp i)))
	   (equal (bits x i 0) x)))

;;The first of the following three lemmas has monotonicity built in, and was
;;already here when the next two were added.  Those next two do not have
;;monotonicity built in but also do not require an integerp hypothesis.

(defthm bits-bvecp
    (implies (and (<= (+ 1 i (- j)) k)
		  (case-split (integerp k)))
	     (bvecp (bits x i j) k)))

(defthm bits-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits x i j) k)))

(defthm bits-bvecp-simple-2
  (bvecp (bits x (1- i) 0) i))

(defun sumbits (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))

(defthmd sumbits-bits
    (implies (and (natp x)
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

(defthm bitn-bits
  (implies (and (<= k (- i j))
		(case-split (<= 0 k))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k)))
	   (equal (bitn (bits x i j) k)
		  (bitn x (+ j k)))))

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

(defthmd bits-shift-down
  (implies (and (<= 0 j)
		(integerp i)
		(integerp j)
		(integerp k))
	   (equal (bits (fl (/ x (expt 2 k))) i j)
		  (bits x (+ i k) (+ j k)))))

(defthm bits-shift-up
  (implies (and (integerp x)
		(integerp k)
		(<= 0 k)
		(integerp i))
	   (equal (* (expt 2 k) (bits x i 0))
		  (bits (* (expt 2 k) x) (+ i k) 0)))
  :rule-classes ())

(defthmd bits-times-2
    (implies (and (acl2-numberp i)
		  (acl2-numberp j))
	     (equal (bits (* 2 x) i j)
		    (bits x (1- i) (1- j)))))

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

(defthmd bitn-plus-bits
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m)))))

(defthm bits-plus-bitn
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ())

(defthmd bits-plus-mult-1
  (implies (and (bvecp x k)
		(<= k m)
		(integerp y)
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp k)))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits y (- n k) (- m k)))))

(defthm bits-plus-mult-2
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

;;The following three lemmas have alternate versions in fadd.lisp:
;;bits-sum-with-gen, bits-sum-3-with-gen, and bits-sum-plus-1-with-prop-gen,
;;respectively.

(defthm bits-sum
  (implies (and (integerp x)
		(integerp y))
	   (equal (bits (+ x y) i j)
		  (bits (+ (bits x i j)
			   (bits y i j)
			   (bitn (+ (bits x (1- j) 0)
				    (bits y (1- j) 0))
				 j))
			(- i j)
			0)))
  :rule-classes ())

(defthm bits-sum-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (bitn (+ (bits x (1- j) 0) (bits y (1- j) 0))
                                 j)
                           (bitn (+ (bits (+ x y) (1- j) 0) (bits z (1- j) 0))
                                 j))
                        (- i j) 0)))
  :rule-classes ())

(defthm bits-sum-plus-1
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp j)
		(>= i j)
		(>= j 0))
	   (equal (bits (+ 1 x y) i j)
		  (bits (+ (bits x i j)
			   (bits y i j)
			   (bitn (+ 1
				    (bits x (1- j) 0)
				    (bits y (1- j) 0))
				 j))
			(- i j) 0)))
  :rule-classes ())

;;bits-dont-match can prove things like this:
;;(thm (implies (equal 7 (bits x 8 6))
;;		(not (equal 4 (bits x 15 6)))))
;;See also bits-match.

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
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  nil)))

;;bits-match can prove things like this:
;;(thm (implies (equal 12 (bits x 15 6))
;;		(equal 4 (bits x 8 6))))
;;See also bits-dont-match.

(defthmd bits-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(equal k (bits k2 (+ i (- j2)) (+ (- j2) j)))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  t)))

(defthm bits-drop-from-minus
  (implies (and (<= y x)
		(bvecp x n)
		(bvecp y n))
	   (equal (bits (+ x (* -1 y)) (1- n) 0)
		  (+ x (* -1 y)))))

(defthmd bits-sum-swallow
  (implies (and (equal (bitn x k) 0)
                (natp x)
                (natp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= i j)
                (> j k)
                (>= k 0)
                (<= y (expt 2 k)))
           (equal (bits (+ x y) i j)
                  (bits x i j))))

;;;**********************************************************************
;;;			     CAT
;;;**********************************************************************

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp m) (< 0 m)
                              (integerp n) (< 0 n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

;;Definition of the macro, cat:

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
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

;;(:type-prescription cat) is no better than cat-nonnegative-integer-type
;;and might be worse:

(in-theory (disable (:type-prescription binary-cat)))

(defthm cat-bvecp
  (implies (and (<= (+ m n) k)
		(case-split (integerp k)))
	   (bvecp (cat x m y n) k)))

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

;;In rel3 we were concerned that the following rule could cause problems when
;;enabled (in particular, size info is lost).  But now that we pass around size
;;arguments so faithfully, this seems less of a concern.

(defthm cat-0
  (implies (and (case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (cat 0 m y n) y)))

;;We can rely on bits-tail to complete the simplification down to x if desired.
;;We used to have cat-x-0-0, but this rule is better:
(defthm cat-with-n-0
  (equal (binary-cat x m y 0)
	 (bits x (1- m) 0)))

;;We can rely on bits-tail to complete the simplification down to x if desired.
(defthm cat-with-m-0
  (equal (binary-cat x 0 y n)
	 (bits y (1- n) 0)))

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


;;;**********************************************************************
;;;			  MULCAT
;;;**********************************************************************

(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription))

;;(:type-prescription mulcat) is no better than mulcat-nonnegative-integer-type
;;and might be worse:

(in-theory (disable (:type-prescription mulcat)))

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


;;;**********************************************************************
;;;			  SETBITN AND SETBITS
;;;**********************************************************************

(defun setbits (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp i)
                              (integerp j)
                              (<= 0 j)
                              (<= j i)
                              (integerp w)
                              (< i w))))
  (mbe :logic (cat (bits x (1- w) (1+ i))
                   (+ -1 w (- i))
                   (cat (bits y (+ i (- j)) 0)
                        (+ 1 i (- j))
                        (bits x (1- j) 0)
                        j)
                   (1+ i))
       :exec  (cond ((int= j 0)
                     (cond ((int= (1+ i) w)
                            (bits y (+ i (- j)) 0))
                           (t
                            (cat (bits x (1- w) (1+ i))
                                 (+ -1 w (- i))
                                 (bits y (+ i (- j)) 0)
                                 (1+ i)))))
                    ((int= (1+ i) w)
                     (cat (bits y (+ i (- j)) 0)
                          (+ 1 i (- j))
                          (bits x (1- j) 0)
                          j))
                    (t
                     (cat (bits x (1- w) (1+ i))
                          (+ -1 w (- i))
                          (cat (bits y (+ i (- j)) 0)
                               (+ 1 i (- j))
                               (bits x (1- j) 0)
                               j)
                          (1+ i))))))

;;SETBITN is rewritten to SETBITS (and thus to CAT) when the index is a constant:

(defthm setbitn-rewrite
  (implies (syntaxp (quotep n))
	   (equal (setbitn x w n y)
		  (setbits x w n n y))))

;;We expect the following rules to be sufficient in any context in which a call
;;to SETBITN is not rewritten:

(defthm setbitn-nonnegative-integer-type
  (and (integerp (setbitn x w n y))
       (<= 0 (setbitn x w n y)))
  :rule-classes (:type-prescription))

;;(:type-prescription setbitn) is no better than setbits-nonnegative-integer-type
;;and might be worse:

(in-theory (disable (:type-prescription setbitn)))

(defthm setbitn-bvecp
  (implies (and (<= w k)
		(case-split (integerp k)))
	   (bvecp (setbitn x w n y) k)))

(defthm bitn-setbitn
  (implies (and (case-split (bvecp y 1))
		(case-split (< 0 w))
		(case-split (< n w))
		(case-split (< k w))
		(case-split (<= 0 k))
		(case-split (integerp w))
		(case-split (integerp n))
		(<= 0 n)
		(case-split (integerp k)))
	   (equal (bitn (setbitn x w n y) k)
		  (if (equal n k)
		      y
		    (bitn x k)))))


;;;**********************************************************************
;;;			  SHFT
;;;**********************************************************************

(defund shft (x s l)
  (declare (xargs :guard (and (integerp s) (rationalp x))))
  (mod (fl (* (expt 2 s) x)) (expt 2 (nfix l))))

(defthm shft-nonnegative-integer-type
  (and (integerp (shft x s l))
       (<= 0 (shft x s l)))
  :rule-classes (:type-prescription))

;;(:type-prescription shft) is no better than shft-nonnegative-integer-type
;;and might be worse:
(in-theory (disable (:type-prescription shft)))

(defthm shft-bvecp
  (implies (and (<= n k)
		(case-split (integerp k)))
	   (bvecp (shft x s n) k)))


;;;**********************************************************************
;;;			  LNOT
;;;**********************************************************************

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

(defthm lnot-nonnegative-integer-type
  (and (integerp (lnot x n))
       (<= 0 (lnot x n)))
  :rule-classes ((:type-prescription :typed-term (lnot x n))))

;;(:type-prescription lnot) is no better than lnot-nonnegative-integer-type
;;and might be worse:

(in-theory (disable (:type-prescription lnot)))

(defthm lnot-bvecp
  (implies (and (<= n k)
		(case-split (integerp k)))
	   (bvecp (lnot x n) k)))

(defthm lnot-lnot
  (implies (and (case-split (natp n))
		(case-split (bvecp x n)))
	   (equal (lnot (lnot x n) n)
		  x)))

(defthmd bitn-lnot
  (implies (and (case-split (natp m))
		(case-split (natp n)))
	   (equal (bitn (lnot x m) n)
		  (if (< n m)
		      (lnot (bitn x n) 1)
		    0))))

(defthmd bits-lnot
  (implies (and (< i m)
		(case-split (natp j))
		(case-split (integerp m))
		(case-split (integerp i)))
	   (equal (bits (lnot x m) i j)
		  (lnot (bits x i j) (1+ (- i j))))))

(defthm bitn-lnot-not-equal
  (implies (and (< k n)
		(integerp n)
		(<= 0 n)
		(integerp k)
		(<= 0 k))
	   (not (= (bitn (lnot x n) k) (bitn x k))))
  :rule-classes ())

(defthmd lnot-times-2
  (implies (and (case-split (natp x))
		(case-split (natp n)))
	   (equal (1+ (* 2 (lnot x n)))
		  (lnot (* 2 x) (1+ n)))))

(defthmd lnot-fl
  (implies (and (<= k n)
		(<= 0 k)
		(integerp n)
		(integerp k))
	   (equal (fl (* (/ (expt 2 k)) (lnot x n)))
		  (lnot (fl (/ x (expt 2 k))) (- n k)))))


;;;**********************************************************************
;;;			  LAND, LIOR, LXOR
;;;**********************************************************************

;;The following recursive formulations support inductive proofs of the
;;properties of the logical operations:

(defthm land-base
  (equal (land x y 1)
         (if (and (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             1
           0))
  :rule-classes ())

(defthm land-def
  (implies (and (integerp x)
		(integerp y)
		(> n 0)
		(integerp n))
	   (equal (land x y n)
		  (+ (* 2 (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
		     (land (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthm lior-base
  (equal (lior x y 1)
         (if (or (equal (bitn x 0) 1)
                 (equal (bitn y 0) 1))
             1
           0))
  :rule-classes ())

(defthm lior-def
    (implies (and (integerp x)
		  (integerp y)
		  (< 0 n)
		  (integerp n))
	     (equal (lior x y n)
		    (+ (* 2 (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
		       (lior (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthm lxor-base
  (equal (lxor x y 1)
         (if (iff (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             0
           1))
  :rule-classes ())

(defthm lxor-def
    (implies (and (integerp x)
		  (integerp y)
		  (< 0 n)
		  (integerp n))
	     (equal (lxor x y n)
		    (+ (* 2 (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
		       (lxor (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthm land-nonnegative-integer-type
  (and (integerp (land x y n))
       (<= 0 (land x y n)))
  :rule-classes (:type-prescription))

;;(:type-prescription land) is no better than land-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-land)))

(defthm lior-nonnegative-integer-type
  (and (integerp (lior x y n))
       (<= 0 (lior x y n)))
  :rule-classes (:type-prescription))

;;(:type-prescription lior) is no better than lior-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lior)))

(defthm lxor-nonnegative-integer-type
  (and (integerp (lxor x y n))
       (<= 0 (lxor x y n)))
  :rule-classes (:type-prescription))

;;(:type-prescription lxor) is no better than lxor-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lxor)))

(defthm land-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (land x y n) k)))

(defthm lior-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (lior x y n) k)))

(defthm lxor-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (lxor x y n) k)))

(defthmd land-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land x y m) (land x y n))))

(defthmd lior-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (< n m)
		  (natp n)
		  (natp m))
	     (equal (lior x y m)
		    (lior x y n))))

(defthmd lxor-reduce
  (implies (and (bvecp x n)
		(bvecp y n)
		(< n m)
		(case-split (integerp m)))
	   (equal (lxor x y m) (lxor x y n))))

(defthmd land-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (land x y n) 2)
		    (land (mod x 2) (mod y 2) 1))))

(defthm land-x-y-0
    (equal (land x y 0) 0))

(defthmd land-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (land x y n) 2))
		    (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

(defthmd lior-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (lior x y n) 2)
		    (lior (mod x 2) (mod y 2) 1))))

(defthm lior-x-y-0
    (equal (lior x y 0) 0))

(defthmd lior-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (lior x y n) 2))
		    (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

(defthmd lxor-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (lxor x y n) 2)
		    (lxor (mod x 2) (mod y 2) 1))))

(defthm lxor-x-y-0
    (equal (lxor x y 0) 0))

(defthmd lxor-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (lxor x y n) 2))
		    (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

;;Some natural induction schemes:

(defun logop-2-induct (x y)
  (if (or (zp x) (zp y))
      ()
    (logop-2-induct (fl (/ x 2)) (fl (/ y 2)))))

(defun logop-2-n-induct (x y n)
  (if (zp n)
      (cons x y)
    (logop-2-n-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))

(defun logop-3-induct (x y z)
  (declare (xargs :measure (:? z y x)))
  (if (and (natp x) (natp y) (natp z))
      (if (and (zp x) (zp y) (zp z))
	  t
	(logop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))

;;Commutativity and associativity:

(defthm land-commutative
  (equal (land y x n)
	 (land x y n)))

(defthm lior-commutative
  (equal (lior y x n)
	 (lior x y n)))

(defthm lxor-commutative
  (equal (lxor y x n)
	 (lxor x y n)))

(defthm land-associative
  (equal (land (land x y n) z n)
	 (land x (land y z n) n)))

(defthm lior-associative
  (equal (lior (lior x y n) z n)
	 (lior x (lior y z n) n)))

(defthm lxor-associative
  (equal (lxor (lxor x y n) z n)
	 (lxor x (lxor y z n) n)))

(defthm land-commutative-2
  (equal (land y (land x z n) n)
	 (land x (land y z n) n)))

(defthm lior-commutative-2
  (equal (lior y (lior x z n) n)
	 (lior x (lior y z n) n)))

(defthm lxor-commutative-2
  (equal (lxor y (lxor x z n) n)
	 (lxor x (lxor y z n) n)))

(defthm land-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (land x (land y z n) n)
		  (land (land x y n) z n))))

(defthm lior-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (lior x (lior y z n) n)
		  (lior (lior x y n) z n))))

(defthm lxor-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (lxor x (lxor y z n) n)
		  (lxor (lxor x y n) z n))))

;;Trivial cases:

(defthm land-self
  (equal (land x x n)
	 (bits x (1- n) 0)))

(defthm lior-self
  (implies (and (case-split (bvecp x n))
		(case-split (integerp n)))
	   (equal (lior x x n) x)))

(defthm lxor-self
  (implies (case-split (bvecp x n))
	   (equal (lxor x x n) 0)))

(defthm land-0
  (equal (land 0 y n)
	 0))

(defthm lior-0
  (implies (case-split (bvecp y n))
	   (equal (lior 0 y n) y)))

(defthmd lior-equal-0
  (implies (and (case-split (bvecp x n))
		(case-split (bvecp y n))
		(case-split (integerp n)))
	   (equal (equal 0 (lior x y n))
		  (and (equal x 0)
		       (equal y 0)))))

(defthmd land-equal-0
  (implies (and (bvecp i 1)
		(bvecp j 1))
	   (equal (equal 0 (land i j 1))
		  (or (equal i 0)
		      (equal j 0)))))

(defthm lxor-0
  (implies (case-split (bvecp y n))
	   (equal (lxor 0 y n) y)))


;;We can rely on bits-tail to complete the simplification down to x if desired.
(defthm land-ones
  (equal (land (1- (expt 2 n)) x n)
	 (bits x (1- n) 0))
  :rule-classes nil)

;;We can rely on bits-tail to complete the simplification down to x if desired.
(defthm land-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
		(equal k (1- (expt 2 n))))
	   (equal (land k x n)
		  (bits x (1- n) 0))))

(defthm lior-ones
  (implies (and (case-split (bvecp x n))
		(case-split (natp n)))
	   (equal (lior (1- (expt 2 n)) x n)
		  (1- (expt 2 n))))
  :rule-classes ())

(defthm lior-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
			      (quotep n)
			      (equal (cadr k) (1- (expt 2 (cadr n))))))
		(force (equal k (1- (expt 2 n))))
		(case-split (natp n))
		(case-split (bvecp x n)))
	   (equal (lior k x n)
		  (1- (expt 2 n)))))

(defthm lxor-ones
  (implies (case-split (bvecp x n))
	   (equal (lxor (1- (expt 2 n)) x n)
		  (lnot x n)))
  :rule-classes ())

(defthm lxor-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
			      (quotep n)
			      (equal (cadr k) (1- (expt 2 (cadr n))))))
		(force (equal k (1- (expt 2 n))))
		(case-split (bvecp x n)))
	   (equal (lxor k x n)
		  (lnot x n))))

;;Bit extraction:

(defthm bits-land
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (land x y n) i j)
		  (land (bits x i j)
			(bits y i j)
			(+ (min n (1+ i)) (- j))))))

(defthm bitn-land
  (implies (and (case-split (<= 0 m))
		(case-split (integerp n)))
	   (equal (bitn (land x y n) m)
		  (if (< m n)
		      (land (bitn x m)
			    (bitn y m)
			    1)
		    0))))

(defthm bits-lior
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (lior x y n) i j)
		  (lior (bits x i j)
			(bits y i j)
			(+ (min n (1+ i)) (- j))))))

(defthm bitn-lior
  (implies (and (case-split (<= 0 m))
		(case-split (integerp n)))
	   (equal (bitn (lior x y n) m)
		  (if (< m n)
		      (lior (bitn x m)
			    (bitn y m)
			    1)
		    0))))

(defthm bits-lxor
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (lxor x y n) i j)
		  (lxor (bits x i j)
			(bits y i j)
			(+ (min n (1+ i)) (- j))))))

(defthm bitn-lxor
  (implies (and (case-split (<= 0 m))
		(case-split (integerp n)))
	   (equal (bitn (lxor x y n) m)
		  (if (< m n)
		      (lxor (bitn x m)
			    (bitn y m)
			    1)
		    0))))

(defthm bitn-lxor-0
    (implies (and (integerp x)
		  (integerp y)
		  (not (zp n)))
	     (= (bitn (lxor x y n) 0)
		(bitn (+ x y) 0)))
  :rule-classes ())

;;Compositions:

(defthmd lior-land-1
  (equal (lior x (land y z n) n)
	 (land (lior x y n) (lior x z n) n)))

(defthmd lior-land-2
  (equal (lior (land y z n) x n)
	 (land (lior x y n) (lior x z n) n)))

(defthmd land-lior-1
  (equal (land x (lior y z n) n)
	 (lior (land x y n) (land x z n) n)))

(defthmd land-lior-2
  (equal (land (lior y z n) x n)
	 (lior (land x y n) (land x z n) n)))

(defthmd lior-land-lxor
  (equal (lior (land x y n) (lior (land x z n) (land y z n) n) n)
	 (lior (land x y n) (land (lxor x y n) z n) n)))

(defthmd lxor-rewrite
  (equal (lxor x y n)
	 (lior (land x (lnot y n) n)
	       (land y (lnot x n) n)
	       n)))

(defthmd lnot-lxor
  (equal (lnot (lxor x y n) n)
	 (lxor (lnot x n) y n)))

;;Inequalities:

(defthm land-bnd
    (implies (case-split (<= 0 x))
	     (<= (land x y n) x))
  :rule-classes (:rewrite :linear))

(defthm lior-bnd
  (implies (case-split (bvecp x n))
	   (<= x (lior x y n)))
  :rule-classes (:rewrite :linear))

(defthm lior-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (lior x y n) m)))

;;Powers of 2:

(defthm lior-plus
    (implies (and (bvecp y m)
		  (bvecp x (- n m))
		  (<= m n)
		  (natp m)
		  (integerp n))
	     (= (lior (* (expt 2 m) x) y n)
		(+ (* (expt 2 m) x) y)))
  :rule-classes ())

(defthm lior-shift
    (implies (and (bvecp x (- n m))
		  (bvecp y (- n m))
		  (integerp n)
		  (natp m)
		  (<= m n))
	     (= (lior (* (expt 2 m) x)
		      (* (expt 2 m) y)
		      n)
		(* (expt 2 m) (lior x y (- n m)))))
  :rule-classes ())

(defthm lior-expt
    (implies (and (natp n)
		  (natp k)
		  (< k n)
		  (bvecp x n))
	     (= (lior x (expt 2 k) n)
		(+ x (* (expt 2 k) (- 1 (bitn x k))))))
  :rule-classes ())

(defthmd land-with-shifted-arg
  (implies (and (integerp x)
		(rationalp y)
		(integerp m)
		(integerp n)
		(<= 0 m))
	   (equal (land (* (expt 2 m) x) y n)
		  (* (expt 2 m) (land x (bits y (1- n) m) (+ n (- m)))))))

(defthmd land-expt
  (implies (and (natp n)
		(natp k)
		(< k n))
	   (equal (land x (expt 2 k) n)
		  (* (expt 2 k) (bitn x k)))))

(defthm land-slice
  (implies (and (< j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (land x (- (expt 2 i) (expt 2 j)) n)
		  (* (expt 2 j) (bits x (1- i) j))))
  :rule-classes ())

(defthmd lior-slice
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior x
                        (- (expt 2 i) (expt 2 j))
                        n)
		  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j))))

(defthmd lior-cat
  (implies (and (case-split (integerp n))
		(case-split (integerp m))
		(> n 0)
		(> m 0)
		(equal l (+ m n)))
	   (equal (lior (cat x1 m y1 n) (cat x2 m y2 n) l)
		  (cat (lior x1 x2 m) m (lior y1 y2 n) n))))

(defthm lior-cat-constant
  (implies (and (case-split (integerp n))
		(case-split (integerp m))
		(syntaxp (quotep c))
		(> n 0)
		(> m 0)
		(equal l (+ m n)))
	   (equal (lior c (cat x2 m y2 n) l)
		  (cat (lior (bits c (+ -1 m n) n) x2 m)
		       m
		       (lior (bits c (1- n) 0) y2 n)
		       n))))

(defthmd lior-bits-1
  (equal (lior (bits x (1- n) 0)
               y
               n)
         (lior x y n)))

(defthmd lior-bits-2
  (equal (lior x
               (bits y (1- n) 0)
               n)
         (lior x y n)))

(defthmd land-bits-1
  (equal (land (bits x (1- n) 0)
               y
               n)
         (land x y n)))

(defthmd land-bits-2
  (equal (land x
               (bits y (1- n) 0)
               n)
         (land x y n)))

(defthmd lxor-bits-1
  (equal (lxor (bits x (1- n) 0)
               y
               n)
         (lxor x y n)))

(defthmd lxor-bits-2
  (equal (lxor x
               (bits y (1- n) 0)
               n)
         (lxor x y n)))

;;;**********************************************************************
;;;			  LOGAND1, LOGIOR1, LOGXOR1
;;;**********************************************************************

(defund logand1 (x n)
  (declare (xargs :guard (integerp n)))
  (log= x (1- (expt 2 n))))

(defund logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(defund logxor1 (src)
  (declare (xargs :guard (integerp src)))
  (if (oddp (logcount src)) 1 0))

(defthm logand1-nonnegative-integer-type
  (and (integerp (logand1 x y))
       (<= 0 (logand1 x y)))
  :rule-classes (:type-prescription))

(defthm logior1-nonnegative-integer-type
  (and (integerp (logior1 x))
       (<= 0 (logior1 x)))
  :rule-classes (:type-prescription))

(defthm logxor1-nonnegative-integer-type
  (and (integerp (logxor1 x))
       (<= 0 (logxor1 x)))
  :rule-classes (:type-prescription))

(defthm logand1-bvecp
  (bvecp (logand1 x y) 1))

(defthm logior1-bvecp
  (bvecp (logior1 x) 1))

(defthm logxor1-bvecp
  (bvecp (logxor1 x) 1))


;;;**********************************************************************
;;;			  LOG=, etc.
;;;**********************************************************************

(defund log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defund log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))

(defund log< (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (< x y) 1 0))

(defund log<= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (<= x y) 1 0))

(defund log> (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (> x y) 1 0))

(defund log>= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (>= x y) 1 0))

(defthm log<-bvecp
  (bvecp (log< x y) 1))

(defthm log<-nonnegative-integer-type
  (and (integerp (log< x y))
       (<= 0 (log< x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log<-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<)))

(defthm log<=-bvecp
  (bvecp (log<= x y) 1))

(defthm log<=-nonnegative-integer-type
  (and (integerp (log<= x y))
       (<= 0 (log<= x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log<=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<=)))

(defthm log>-bvecp
  (bvecp (log> x y) 1))

(defthm log>-nonnegative-integer-type
  (and (integerp (log> x y))
       (<= 0 (log> x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log>-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log>)))

(defthm log>=-bvecp
  (bvecp (log>= x y) 1))

(defthm log>=-nonnegative-integer-type
  (and (integerp (log>= x y))
       (<= 0 (log>= x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log>=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log>=)))

(defthm log=-bvecp
  (bvecp (log= x y) 1))

(defthm log=-nonnegative-integer-type
  (and (integerp (log= x y))
       (<= 0 (log= x y)))
  :rule-classes (:type-prescription))

(defthm log=-commutative
  (equal (log= x y)
	 (log= y x)))

;;This rule is no better than log=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log=)))

(defthm log<>-bvecp
  (bvecp (log<> x y) 1))

(defthm log<>-nonnegative-integer-type
  (and (integerp (log<> x y))
       (<= 0 (log<> x y)))
  :rule-classes (:type-prescription))

(defthm log<>-commutative
  (equal (log<> x y)
	 (log<> y x)))

;;This rule is no better than log<>-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<>)))

(defthm log=-cat-constant
  (implies (and (syntaxp (quotep k))
		(case-split (bvecp k (+ m n)))
		(case-split (bvecp x m))
		(case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (<= 0 n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (log= k (cat x m y n))
		  (land (log= x (bits k (+ -1 m n) n))
			(log= y (bits k (1- n) 0))
			1))))


;;;**********************************************************************
;;;			  ENCODE, DECODE
;;;**********************************************************************

(defund decode (x n)
  (declare (xargs :guard (rationalp n)))
  (if (and (natp x) (< x n))
      (ash 1 x)
    0))

(defund encode (x n)
    (declare (xargs :guard (and (acl2-numberp x)
                                (integerp n)
                                (<= 0 n))))
  (if (zp n)
      0
    (if (= x (ash 1 n))
        n
      (encode x (1- n)))))

(defthm encode-bvecp
  (implies (and (< n (expt 2 k))
		(case-split (integerp k)))
	   (bvecp (encode x n) k)))

(defthm encode-nonnegative-integer-type
  (and (integerp (encode x n))
       (<= 0 (encode x n)))
  :rule-classes (:type-prescription))

;;This rule is no better than encode-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription encode)))

(defthm decode-nonnegative-integer-type
  (and (integerp (decode x n))
       (<= 0 (decode x n)))
  :rule-classes (:type-prescription))

;;This rule is no better than decode-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription decode)))

(defthm decode-bvecp
  (implies (and (<= n k)
		(case-split (integerp k)))
	   (bvecp (decode x n) k)))

