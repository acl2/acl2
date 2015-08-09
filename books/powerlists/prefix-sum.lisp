#|
This book proves the correctness of two parallel prefix sum computations,
including the Ladner-Fischer algorithm.  The events are described in the paper
"Defthms About Zip and Tie", UTCS tech report TR97-02.

To compile it, I do the following:

    (ld ;; newline to fool dependency scanner
     "defpkg.lisp")
    (certify-book "prefix-sum" 4)
    (in-package "POWERLISTS")

|#


(in-package "POWERLISTS")
(include-book "algebra" :load-compiled-file nil)
(include-book "simple" :load-compiled-file nil)
(include-book "arithmetic/top" :dir :system :load-compiled-file nil)

(set-verify-guards-eagerness 2)

;;; To begin with, we define a binary associative operator with a left
;;; identity.  Note, it is not possible for both "0+x=x" and "x+y is of the
;;; right type" to be true.  It is tempting to make the first of these theorems
;;; true, but that would be a Bad Thing.  Most ACL2 binary operators
;;; (e.g. plus, and, ...) take the second theorem as true and violate the
;;; first.  Since we mean for this book to be _useful_ in later work, we follow
;;; the ACL2 conventions.

(encapsulate
 ((domain-p (x) t)
  (bin-op (x y) t)
  (left-zero () t))

 (local (defun domain-p (x)  (integerp x)))
 (local (defun bin-op (x y)  (+ (ifix x) (ifix y))))
 (local (defun left-zero () 0))

 (defthm booleanp-domain-p
   (booleanp (domain-p x))
   :rule-classes (:rewrite :type-prescription))

 (defthm scalar-left-zero
   (domain-p (left-zero))
   :rule-classes (:rewrite :type-prescription))

 (defthm domain-powerlist
   (implies (domain-p x)
	    (not (powerlist-p x))))

 (defthm left-zero-identity
   (implies (domain-p x)
	    (equal (bin-op (left-zero) x) x)))

 (defthm bin-op-assoc
   (equal (bin-op (bin-op x y) z)
	  (bin-op x (bin-op y z))))

 (defthm scalar-bin-op
   (domain-p (bin-op x y))
   :rule-classes (:rewrite :type-prescription))
)

;;; We extend the notion of "domain" to include powerlists.  It's sad that we
;;; have to define these functions, since they're instances of generic
;;; functions in algebra.lisp.  Ah well....

(defun p-domain-list-p (x)
  (if (powerlist-p x)
      (and (p-domain-list-p (p-untie-l x)) (p-domain-list-p (p-untie-r x)))
    (domain-p x)))
(in-theory (disable (p-domain-list-p)))

(defthm domain-list-zip
  (equal (p-domain-list-p (p-zip x y))
	 (and (p-domain-list-p x)
	      (p-domain-list-p y)))
  :hints (("Goal"
	   :by (:functional-instance zip-b-tie-list-of-type-fn
				     (b-tie-list-of-type-fn p-domain-list-p)
				     (type-fn domain-p)))))

(defthm domain-list-tie
  (equal (p-domain-list-p (p-tie x y))
	 (and (p-domain-list-p x)
	      (p-domain-list-p y)))
  :hints (("Goal"
	   :by (:functional-instance tie-b-tie-list-of-type-fn
				     (b-tie-list-of-type-fn p-domain-list-p)
				     (type-fn domain-p)))))

(defthm domain-list-unzip
  (implies (and (powerlist-p x)
		(p-domain-list-p x))
	   (and (p-domain-list-p (p-unzip-l x))
		(p-domain-list-p (p-unzip-r x))))
  :hints (("Goal"
	   :use (:functional-instance unzip-b-tie-list-of-type-fn
				      (b-tie-list-of-type-fn p-domain-list-p)
				      (type-fn domain-p)))))

(defthm domain-list-untie
  (implies (and (powerlist-p x)
		(p-domain-list-p x))
	   (and (p-domain-list-p (p-untie-l x))
		(p-domain-list-p (p-untie-r x))))
  :hints (("Goal"
	   :use (:functional-instance untie-b-tie-list-of-type-fn
				      (b-tie-list-of-type-fn p-domain-list-p)
				      (type-fn domain-p)))))

;;; We're going to define the basic (sequential) prefix sum function.  This
;;; will be our "specification."  There are several equivalent ways to define
;;; it.  Note, first of all, that the basic "ps(x1|x2)=ps(x1)|ps(x2)"
;;; definition doesn't work.  The reason is that the right half of ps(x1|x2) is
;;; not a prefix sum (of x2 or anything else).  Instead, it is a "raised"
;;; prefix sum.  I.e., we can get it from ps(x2) by adding some number (sum(x1)
;;; as it turns out) to all its elements.  So, we have to come up with a more
;;; subtle definition.  One approach (as hinted) is
;;;
;;;      ps(x1|x2) = ps(x1)|{ps(x2)+sum(x1)}
;;;
;;; but this isn't immediately obvious, and so it'd be a bad spec.  Another way
;;; to think of the problem is to think of "carrying" some value from ps(x1) to
;;; ps(x2).  This "carry bit" has the effect of raising ps(x2) by sum(x1).  So,
;;; we could write
;;;
;;;      ps(c, x1|x2) = ps(c, x1) | ps(carry(c, x1), x2)
;;;
;;; Now, carry(c, x1) is precisely sum(x1), i.e., the amount we have to lift
;;; each element of ps(x2) by to put it in the same "scale" as ps(x1).  But the
;;; way to do this sequentially isn't to compute a carry value, but to take the
;;; last value of ps(c, x1).  I.e., to compute the prefix sum (sequentially),
;;; we keep track of the prefix sum "so far".  So, our target definition
;;; becomes the following
;;;
;;;      ps(c, x1|x2) = ps(c, x1) | ps(last(ps(c, x1)), x2)
;;;
;;; Of course, what we're really interested in is ps(0, x).

(defun p-first (x)
  (if (powerlist-p x)
      (p-first (p-untie-l x))
    x))
(in-theory (disable (p-first)))

(defun p-last (x)
  (if (powerlist-p x)
      (p-last (p-untie-r x))
    x))
(in-theory (disable (p-last)))

(defun p-prefix-sum-aux (prefix x)
  (if (powerlist-p x)
      (p-tie (p-prefix-sum-aux prefix (p-untie-l x))
	     (p-prefix-sum-aux (p-last (p-prefix-sum-aux
					prefix
					(p-untie-l x)))
			       (p-untie-r x)))
    (bin-op prefix x)))
(in-theory (disable (p-prefix-sum-aux)))

(defmacro p-prefix-sum (x)
  `(p-prefix-sum-aux (left-zero) ,x))

;;; It turns out to be enormously useful to think of shifted prefix sums.  This
;;; is because prefix sums and shifts commute.  We will see later, that when
;;; relating prefix sums to zip/unzip, it is easier to think of the right unzip
;;; and then derive the left unzip as the right unzip of a shift.

(defun p-shift (val x)
  (if (powerlist-p x)
      (p-tie (p-shift val (p-untie-l x))
	     (p-shift (p-last (p-untie-l x))
		      (p-untie-r x)))
    val))
(in-theory (disable (p-shift)))

;;; Now, we want to prove that ps(shift(x)) = shift(ps(x)), but before we can
;;; do that, we need to prove some more mundane theorems.

(defthm first-shift
  (implies (not (powerlist-p x))
	   (equal (p-first (p-shift x y)) x)))

(defthm domain-p-last-prefix-sum
  (domain-p (p-last (p-prefix-sum-aux cin x))))

(defthm domain-p-last
  (implies (p-domain-list-p x)
	   (domain-p (p-last x)))
  :rule-classes (:rewrite :type-prescription))

(defthm p-domain-list-p-p-shift
  (implies (and (domain-p cin)
		(p-domain-list-p x))
	   (p-domain-list-p (p-shift cin x))))

(defthm binop-last-shift-prefix-sum
  (implies (domain-p c)
	   (equal (bin-op (p-last
			   (p-shift
			    c (p-prefix-sum-aux c x)))
			  (p-last x))
		  (p-last (p-prefix-sum-aux c x)))))

(defun p-prefix-sum-p-shift-induction-hint (c1 c2 x)
  (if (powerlist-p x)
      (list (p-prefix-sum-p-shift-induction-hint c1 c2 (p-untie-l x))
	    (p-prefix-sum-p-shift-induction-hint
	     (p-last (p-shift (bin-op c1 c2)
			      (p-prefix-sum-aux (bin-op c1 c2)
						(p-untie-l x))))
	     (p-last (p-untie-l x))
	     (p-untie-r x)))
    (list c1 c2)))

(defthm similar-prefix-sum-aux
  (p-similar-p (p-prefix-sum-aux val x) x))

;;; And now, as promised, prefix sums and shifts commute

(defthm p-prefix-sum-p-shift
  (implies (and (domain-p c1)
                (domain-p c2)
                (p-domain-list-p x))
           (equal (p-prefix-sum-aux c1 (p-shift c2 x))
                  (p-shift (bin-op c1 c2)
                           (p-prefix-sum-aux
                            (bin-op c1 c2)
                            x))))
  :hints (("Goal"
           :induct (p-prefix-sum-p-shift-induction-hint c1 c2 x)
           :do-not '(eliminate-destructors))))

;;; The trick to computing prefix sums in parallel is to take the prefix sums
;;; of lists made up of the sum of adjacent pairs.  I.e., to find the prefix
;;; sum of (x1 x2 x3 x4), we consider the prefix sum of (x1+x2 x3+x4) and of
;;; (x1 x2+x3).  So, we define the functions that add adjacent pairs.  Notice
;;; how the function to get the "right" pairs is much easier to deal with.
;;; This is because if doesn't have to carry information from the left half of
;;; the powerlist to the right half.

(defun p-add-left-pairs (val x)
  (if (powerlist-p x)
      (if (powerlist-p (p-untie-l x))
	  (p-tie (p-add-left-pairs val (p-untie-l x))
		 (p-add-left-pairs (p-last
				    (p-untie-l x))
				   (p-untie-r x)))
	(bin-op val (p-untie-l x)))
    (bin-op val x)))
(in-theory (disable (p-add-left-pairs)))

(defun p-add-right-pairs (x)
  (if (powerlist-p x)
      (if (powerlist-p (p-untie-l x))
	  (p-tie (p-add-right-pairs (p-untie-l x))
		 (p-add-right-pairs (p-untie-r x)))
	(bin-op (p-untie-l x) (p-untie-r x)))
    x))
(in-theory (disable (p-add-right-pairs)))

;;; As we mentioned, it is too painful to think about left-pairs, so we'll use
;;; shift to convert it to right-pairs.  This is a big win, since we already
;;; saw shift has nice properties with respect to prefix sum.

(defthm powerlist-shift
  (implies (not (powerlist-p val))
	   (equal (powerlist-p (p-shift val x))
		  (powerlist-p x))))

(defthm p-add-left-pairs->p-add-right-pairs-p-shift
  (implies (and (domain-p val)
		(powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-add-left-pairs val x)
		  (p-add-right-pairs (p-shift val x)))))

;;; Ok now, we want to prove that the right unzip of ps(x) is equal to
;;; ps(arp(x)), where arp(x) is the right-pairs sum of adjacent pairs in x.
;;; The first step is to show that at least they have the same last element.
;;; This is the critical lemma in the induction to follow.

(defthm p-last-p-prefix-sum-p-add-right-pairs
  (implies (and (domain-p val)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-last (p-prefix-sum-aux
			   val
			   (p-add-right-pairs x)))
		  (p-last (p-prefix-sum-aux val x)))))

(defun prefix-sum-p-add-right-pairs-induction-hint (val x)
  (if (powerlist-p x)
    (if (powerlist-p (p-untie-l x))
	(list (prefix-sum-p-add-right-pairs-induction-hint val (p-untie-l x))
	      (prefix-sum-p-add-right-pairs-induction-hint
	       (p-last (p-prefix-sum-aux val (p-untie-l x)))
	       (p-untie-r x)))
      val)
    x))

(defthm powerlist-prefix-sum-aux
  (equal (powerlist-p (p-prefix-sum-aux val x))
	 (powerlist-p x)))

;;; ACL2 gets confused in the base case, since it doesn't look down far
;;; enough.  To help it along, we prove the base case separately.

(defthm prefix-sum-p-add-right-pairs-base
  (implies (and (domain-p val)
		(powerlist-p x)
		(not (powerlist-p (p-untie-l x)))
		(p-regular-p x)
		(p-domain-list-p x))
	   (and (equal (p-prefix-sum-aux
			val
			(p-add-right-pairs x))
		       (bin-op val
			       (bin-op (p-untie-l x)
				       (p-untie-r x))))
		(equal (p-unzip-r
			(p-prefix-sum-aux val x))
		       (bin-op val
			       (bin-op (p-untie-l x)
				       (p-untie-r x))))
		)))

;;; Now, we can prove that the right unzip of the prefix sum is given by the
;;; prefix sum of the right-pairs of the powerlist.  This is really the key
;;; theorem that makes the parallel algorithms work.

(defthm prefix-sum-p-add-right-pairs
  (implies (and (domain-p val)
		(powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-prefix-sum-aux
		   val
		   (p-add-right-pairs x))
		  (p-unzip-r
		   (p-prefix-sum-aux val x))))
  :hints (("Goal" :induct (prefix-sum-p-add-right-pairs-induction-hint val x))))

;;; Next, we look at the left unzip of the prefix sum.  We get this by using
;;; the previous theorem and shifting powerlists using the fact that shift and
;;; prefix sums commute.

(defthm not-powerlist-last
  (not (powerlist-p (p-last x))))

(defthm p-unzip-r-p-shift
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(not (powerlist-p val)))
	   (equal (p-unzip-r (p-shift val x))
		  (p-unzip-l x))))

(defthm p-similar-shift
  (implies (not (powerlist-p val))
	   (p-similar-p (p-shift val x) x)))

(defthm p-regular-shift
  (implies (not (powerlist-p val))
	   (equal (p-regular-p (p-shift val x))
		  (p-regular-p x)))
  :hints (("Goal"
	   :use ((:instance similar-regular (x (p-shift val x)) (y x))
		 (:instance similar-regular (x x) (y (p-shift val x))))
	   :in-theory (disable similar-regular))))

(defthm p-regular-prefix-sum
  (equal (p-regular-p (p-prefix-sum-aux val x))
	 (p-regular-p x))
  :hints (("Goal"
	   :use ((:instance similar-regular (x (p-prefix-sum-aux val x)) (y x))
		 (:instance similar-regular (x x) (y (p-prefix-sum-aux val x))))
	   :in-theory (disable similar-regular))))

(defthm prefix-sum-p-add-left-pairs
  (implies (and (p-regular-p x)
		(p-domain-list-p x)
		(powerlist-p x)
		(domain-p val1)
		(domain-p val2))
	   (equal (p-prefix-sum-aux val1
				    (p-add-left-pairs
				     val2 x))
		  (p-unzip-l
		   (p-prefix-sum-aux (bin-op val1 val2)
				     x)))))

;;; Now, we're ready to define the first parallel prefix sum algorithm.  This
;;; algorithm is also based on shifting powerlists, but its written entirely in
;;; terms of zip.  In particular, we require a version of shift that uses only
;;; zip.  Misra calls this the "star" function.  We'll also need a function to
;;; take the pairwise sum of two powerlists.

(defun p-star (x)
  (if (powerlist-p x)
      (p-zip (p-star (p-unzip-r x)) (p-unzip-l x))
    (left-zero)))
(in-theory (disable (p-star)))

(defun p-add (x y)
  (declare (xargs :guard (p-similar-p x y)))
  (if (powerlist-p x)
      (p-zip (p-add (p-unzip-l x) (p-unzip-l y))
	     (p-add (p-unzip-r x) (p-unzip-r y)))
    (bin-op x y)))
(in-theory (disable (p-add)))

(defmacro p-add-star (x y)
  `(p-add (p-star ,x) ,y))

;;; Unfortunately, the recursion is based on ps(x) -> ps (unzip (x + *x))
;;; and it's not obvious that unzip(x + *x) is smaller than x.  The trick is to
;;; discover that *x is the same size as x, hence x+*x is the same size as x,
;;; and so unzip(x + *x) is smaller than x.  The notion of size we mean is the
;;; number of elements in a list (in particular, we can't say anything about
;;; acl2-count, since we don't know what bin-op does).  So, we begin with
;;; defining a custom measure and proving the relevant lemmas.

(defthm powerlist-star
  (equal (powerlist-p (p-star x))
	 (powerlist-p x)))

(defthm similar-star
  (implies (p-regular-p x)
	   (p-similar-p (p-star x) x)))

(defthm similar-add
  (implies (p-similar-p x y)
	   (p-similar-p (p-add x y) x)))

(defun p-measure (x)
  (if (powerlist-p x)
      (+ (p-measure (p-unzip-l x))
	 (p-measure (p-unzip-r x)))
    1))
(in-theory (disable (p-measure)))

(defthm p-measure-bounds-1
  (<= 1 (p-measure x))
  :rule-classes (:linear :rewrite))

(defthm p-measure-bounds-2
  (implies (powerlist-p x)
	   (<= 2 (p-measure x)))
  :rule-classes (:linear :rewrite))

(defthm measure-similar
  (implies (p-similar-p x y)
	   (equal (p-measure x) (p-measure y)))
  :hints (("Goal"
	   :induct (unzip-on-x-and-y x y))))

(defthm measure-star
  (equal (p-measure (p-star x)) (p-measure x))
  :rule-classes (:linear :rewrite))

(defthm measure-add
  (<= (p-measure (p-add x y)) (p-measure x))
  :rule-classes (:linear :rewrite))

(defthm measure-unzip-add-star
  (implies (powerlist-p x)
	   (and (< (p-measure (p-unzip-l (p-add (p-star x) x)))
		   (p-measure x))
		(< (p-measure (p-unzip-r (p-add (p-star x) x)))
		   (p-measure x)))))

(defthm similar-add-star
  (implies (p-regular-p x)
	   (p-similar-p (p-add (p-star x) x) x))
  :hints (("Goal"
	   :use ((:instance similar-star)
		 (:instance similar-add (x (p-star x)) (y x)))
	   :in-theory (disable similar-star similar-add))))

(defthm regular-add-star
  (implies (p-regular-p x)
	   (p-regular-p (p-add (p-star x) x)))
  :hints (("Goal"
	   :use ((:instance similar-regular (y (p-add (p-star x) x))))
	   :in-theory (disable similar-regular))))

;;; Now, we're ready to introduce our parallel prefix sum.  This algorithm is
;;; simply gorgeous!

(defun p-simple-prefix-sum (x)
  (declare (xargs :measure (p-measure x)
		  :guard (p-regular-p x)))
  (if (powerlist-p x)
      (let ((y (p-add (p-star x) x)))
	(p-zip (p-simple-prefix-sum (p-unzip-l y))
	       (p-simple-prefix-sum (p-unzip-r y))))
    x))
(in-theory (disable (p-simple-prefix-sum)))

;;; The first step in the proof is to identify star with shift.  I.e., star is
;;; nothing more than the shift function in disguise.

(defthm last-zip
  (implies (p-similar-p x y)
	   (equal (p-last (p-zip x y)) (p-last y))))

(defthm shift-zip
  (implies (p-similar-p x y)
	   (equal (p-shift val (p-zip x y))
		  (p-zip (p-shift val y) x))))

(defthm shift-zip-regular
  (implies (and (powerlist-p x) (p-regular-p x))
	   (equal (p-shift val x)
		  (p-zip (p-shift val (p-unzip-r x)) (p-unzip-l x))))
  :hints (("Goal"
	   :use (regular-similar-unzip-untie
		 (:instance shift-zip (x (p-unzip-l x)) (y (p-unzip-r x))))
	   :in-theory (disable regular-similar-unzip-untie shift-zip))))

(defthm shift->star
  (implies (p-regular-p x)
	   (equal (p-shift (left-zero) x)
		  (p-star x)))
  :hints (("Goal"
	   :induct (p-star x))))

(in-theory (disable shift-zip shift-zip-regular))

;;; Similarly, we identify add with add-tie.  This is nothing more than an
;;; instance of one of our generic lemmas in algebra.lisp.

(defun p-add-tie (x y)
  (declare (xargs :guard (p-similar-p x y)))
  (if (powerlist-p x)
      (p-tie (p-add-tie (p-untie-l x) (p-untie-l y))
	     (p-add-tie (p-untie-r x) (p-untie-r y)))
    (bin-op x y)))
(in-theory (disable (p-add-tie)))

(defthm add-add-tie
  (implies (p-similar-p x y)
	   (equal (p-add x y) (p-add-tie x y)))
  :hints (("Goal" :in-theory (disable zip-unzip))))

;;; A wonderful lemma finds a different way to add adjacent terms of a
;;; powerlists, this time based on zip instead of tie.  Naturally, this will be
;;; useful when reasoning about simple-prefix-sum, since it's defined entirely
;;; in terms of zip.

(defthm add-right-pairs->add-unzips
  (implies (and (powerlist-p x)
		(p-regular-p x))
	   (equal (p-add-right-pairs x)
		  (p-add (p-unzip-l x) (p-unzip-r x)))))

(in-theory (disable add-add-tie))

;;;; So now, we characterize x + *x as the zip of the adjacent sums.  I.e., for
;;;; x = (x1 x2 x3 x4), we get x+*x = (x1 x1+x2 x2+x3 x3+x4) which is the zip
;;;; of (x1 x2+x3) and (x1+x2 x3+x4) which are the adjacent sums.

(defthm zip-uzl-star-uzl
  (implies (powerlist-p x)
	   (equal (p-zip (p-unzip-l (p-star x)) (p-unzip-l x))
		  (p-star x))))

(defthm zip-uzr-star-uzr
  (implies (powerlist-p x)
	   (equal (p-zip (p-unzip-r (p-star x)) (p-unzip-r x))
		  x)))

(defthm zip-add
  (equal (p-zip (p-add x1 x2) (p-add y1 y2))
	 (p-add (p-zip x1 y1) (p-zip x2 y2))))

(defthm regular-star
  (implies (p-regular-p x)
	   (p-regular-p (p-star x)))
  :hints (("Subgoal *1/2'"
	   :use ((:instance zip-regular
			    (x (p-star (p-unzip-r x)))
			    (y (p-unzip-l x)))
		 (:instance similar-star
			    (x (p-unzip-r x))))
	   :in-theory (disable zip-regular similar-star))))

(defthm zip-add-left-pairs-add-right-pairs
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-zip (p-add-left-pairs (left-zero)
					   x)
			 (p-add-right-pairs x))
		  (p-add (p-star x) x))))

(in-theory (disable zip-add))

(defthm unzip-l-add-star
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-unzip-l (p-add (p-star x) x))
		  (p-add-left-pairs (left-zero) x)))
  :hints (("Goal"
	   :use zip-add-left-pairs-add-right-pairs
	   :in-theory (disable zip-add-left-pairs-add-right-pairs))))

(defthm unzip-r-add-star
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-unzip-r (p-add (p-star x) x))
		  (p-add-right-pairs x)))
  :hints (("Goal"
	   :use zip-add-left-pairs-add-right-pairs
	   :in-theory (disable zip-add-left-pairs-add-right-pairs))))

;;; Now, we're almost ready to tackle the main theorem.  First, we take care of
;;; some simple lemmas needed to discharge the induction hypothesis in the
;;; induction to come.

(defthm domain-list-star
  (implies (p-domain-list-p x)
	   (p-domain-list-p (p-star x))))

(defthm domain-list-add
  (p-domain-list-p (p-add x y)))

(defthm powerlist-p-add
  (equal (powerlist-p (p-add x y))
	 (powerlist-p x)))

(defthm domain-list-unzip-add
  (implies (powerlist-p x)
	   (and (p-domain-list-p (p-unzip-l (p-add x y)))
		(p-domain-list-p (p-unzip-r (p-add x y)))))
  :hints (("Goal"
	   :use ((:instance domain-list-unzip (x (p-add x y))))
	   :in-theory (disable domain-list-unzip))))

(defthm regular-add
  (implies (and (p-regular-p x)
		(p-similar-p x y))
	   (p-regular-p (p-add x y)))
  :hints (("Goal"
	   :use ((:instance similar-regular (y (p-add x y)))
		 (:instance similar-add))
	   :in-theory (disable similar-regular
			       similar-add))))

(defthm regular-unzip-add
  (implies (and (p-regular-p x)
		(p-similar-p x y))
	   (and (p-regular-p (p-unzip-l (p-add x y)))
		(p-regular-p (p-unzip-r (p-add x y)))))
  :hints (("Goal"
	   :use ((:instance unzip-regular (x (p-add x y))))
	   :in-theory (disable unzip-regular))))

(defthm regular-unzip-add-star
  (implies (and (p-regular-p x)
		(p-similar-p x y))
	   (and (p-regular-p (p-unzip-l (p-add (p-star x) y)))
		(p-regular-p (p-unzip-r (p-add (p-star x) y)))))
  :hints (("Goal"
	   :use ((:instance regular-unzip-add (x (p-star x))))
	   :in-theory (disable regular-unzip-add))))

(defthm regular-unzip-add-star-useful
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (and (p-regular-p (p-add-left-pairs (left-zero) x))
		(p-regular-p (p-add-right-pairs x))))
  :hints (("Goal"
	   :use ((:instance regular-unzip-add-star (y x)))
	   :in-theory (disable regular-unzip-add-star))))

(defthm domain-list-unzip-add-star
  (implies (powerlist-p x)
	   (and (p-domain-list-p (p-unzip-l (p-add (p-star x) y)))
		(p-domain-list-p (p-unzip-r (p-add (p-star x) y)))))
  :hints (("Goal"
	   :use ((:instance domain-list-unzip-add (x (p-star x))))
	   :in-theory (disable domain-list-unzip-add))))

(defthm domain-list-unzip-add-star-useful
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (and (p-domain-list-p (p-add-left-pairs (left-zero) x))
		(p-domain-list-p (p-add-right-pairs x))))
  :hints (("Goal"
	   :use ((:instance domain-list-unzip-add-star (y x)))
	   :in-theory (disable domain-list-unzip-add-star))))

(in-theory (disable p-add-left-pairs->p-add-right-pairs-p-shift
		    add-right-pairs->add-unzips))

;;; Finally, we can prove the correctness of our parallel prefix sum.

(defthm simple-prefix-sum-prefix-sum
  (implies (and (p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-simple-prefix-sum x)
		  (p-prefix-sum x)))
  :hints (("Goal"
	   :induct (p-simple-prefix-sum x))))

;;; Next, we introduce another parallel prefix sum, this one due to Ladner and
;;; Fischer.  At first, it is not obvious why this computation is correct!
;;; This definition clearly contrasts with the "simple" one above!

(defun p-lf-prefix-sum (x)
  (declare (xargs :measure (p-measure x)
		  :guard (p-regular-p x)
		  :verify-guards nil))
  (if (powerlist-p x)
      (let ((y (p-lf-prefix-sum
		(p-add (p-unzip-l x) (p-unzip-r x)))))
	(p-zip (p-add (p-star y) (p-unzip-l x)) y))
    x))
(in-theory (disable (p-lf-prefix-sum)))

;;; A quick theorem is that (under the induction hypothesis to come) the right
;;; unzip of the Ladner-Fischer scheme is correct.  This follows, since it's
;;; (ps (+ uzl(x) uzr(x))) and we've already proved this is equal to
;;; (ps arp(x)), which is in turn equal to uzr(ps(x))

(in-theory (enable add-right-pairs->add-unzips))
(defthm unzip-r-lf-prefix-sum
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x)
		(equal
		 (p-lf-prefix-sum (p-add (p-unzip-l x)
					 (p-unzip-r x)))
		 (p-prefix-sum (p-add (p-unzip-l x)
				      (p-unzip-r x)))))
	   (equal
	    (p-lf-prefix-sum (p-add (p-unzip-l x)
				    (p-unzip-r x)))
	    (p-unzip-r (p-prefix-sum x))))
  :hints (("Goal"
	   :use ((:instance prefix-sum-p-add-right-pairs (val (left-zero))))
	   :in-theory (disable prefix-sum-p-add-right-pairs))))

(in-theory (disable add-right-pairs->add-unzips))

(in-theory (disable unzip-l-add-star unzip-r-add-star))

;;; Now, we want to tackle the left unzip of the Ladner-Fischer scheme.  For
;;; that, we need a key lemma:
;;;
;;;       *ps(x) + x = ps(x)
;;;
;;; Misra calls this the "Defining Equation" of prefix sum, though I don't feel
;;; the equation by itself is a suitable definition.  In any case, we need the
;;; result here, so we prove it.  It's easier to do, of course, in terms of tie
;;; so we'll do that first.  Then, we'll translate it into the zip versions.

(defthm shift-prefix-sum
  (implies (and (domain-p val)
		(p-domain-list-p x))
	   (equal (p-add-tie (p-shift val (p-prefix-sum-aux val x)) x)
		  (p-prefix-sum-aux val x))))

(defthm add-star-add-tie-shift
  (implies (and (p-regular-p x)
		(p-similar-p x y))
	   (equal (p-add (p-star x) y)
		  (p-add-tie (p-shift (left-zero) x)
			     y)))
  :hints (("Goal" :use ((:instance similar-star)
			(:instance add-add-tie (x (p-star x)))
			(:instance shift->star))))
  :rule-classes nil)

(defthm add-star-prefix-sum
  (implies (and (p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-add (p-star (p-prefix-sum x)) x)
		  (p-prefix-sum x)))
  :hints (("Goal" :use (:instance add-star-add-tie-shift
				  (x (p-prefix-sum x))
				  (y x))
	   :in-theory (disable shift->star))))

;;; We need one more fact.  The left unzip of the Ladner Fischer scheme is
;;; defined in terms of the right unzip of x.  This is a Bad Thing, since it's
;;; much simpler to reason about the "left unzip" or the "right unzip" than about
;;; a mixture of the two.  So, we use the shift operator to force everything to
;;; be in terms of the "left unzip" only.

(defthm unzip-l-star
  (equal (p-unzip-l (p-star x)) (p-star (p-unzip-r x)))
  :hints (("Goal"
	   :in-theory (disable (p-star)))))

(defthm add-star-unzip-r-prefix->unzip-l-add-star-prefix-sum
  (implies (powerlist-p x)
	   (equal (p-add (p-star (p-unzip-r (p-prefix-sum x)))
			 (p-unzip-l x))
		  (p-unzip-l (p-add (p-star (p-prefix-sum x)) x)))))

(defthm zip-of-equals-is-equal
  (implies (equal (p-zip x1 x2) y)
	   (equal x1 (p-unzip-l y)))
  :rule-classes nil)

(defthm add-star-prefix-unzip-r-prefix-sum
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-add (p-star (p-unzip-r (p-prefix-sum x)))
			 (p-unzip-l x))
		  (p-unzip-l (p-prefix-sum x))))
  :hints (("Goal"
	   :use (add-star-unzip-r-prefix->unzip-l-add-star-prefix-sum
		 add-star-prefix-sum)
	   :in-theory (disable add-star-unzip-r-prefix->unzip-l-add-star-prefix-sum
			       add-star-prefix-sum))
	  ("Goal'''"
	   :by (:instance zip-of-equals-is-equal
			  (x1 (p-add (p-star (p-unzip-r (p-prefix-sum-aux (left-zero) x)))
				     (p-unzip-l x)))
			  (x2 (p-add (p-unzip-l (p-prefix-sum-aux (left-zero) x))
				     (p-unzip-r x)))
			  (y (p-prefix-sum-aux (left-zero) x))))))

;;; Finally, we can prove the correctness of the left unzip of the
;;; Ladner-Fischer scheme, assuming the induction hypothesis hold.

(defthm unzip-l-lf-prefix-sum
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-domain-list-p x)
		(equal (p-lf-prefix-sum (p-add (p-unzip-l x)
							   (p-unzip-r x)))
		       (p-prefix-sum (p-add (p-unzip-l x) (p-unzip-r x)))))
	   (equal (p-add (p-star (p-lf-prefix-sum (p-add
							       (p-unzip-l x)
							       (p-unzip-r x))))
			 (p-unzip-l x))
		  (p-unzip-l (p-prefix-sum x)))))

;;; Combining the two halves gives the correctness of the Ladner-Fischer
;;; scheme.  This is a simple inductive proof, and what ACL2 is best at.

(defthm lf-prefix-sum-prefix-sum
  (implies (and (p-regular-p x)
		(p-domain-list-p x))
	   (equal (p-lf-prefix-sum x)
		  (p-prefix-sum x)))
  :hints (("Goal"
	   :induct (p-lf-prefix-sum x))))
