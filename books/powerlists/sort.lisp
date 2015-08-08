#|

This is in an ACL2 "book" describing in general what it means to be a sort.
Our definition of sorted uses a total ordering on the elements that are allowed
in the powerlists.  That is, we restrict ourselves to powerlists of numbers
and consider the powerlist sorted with respect to <=.  One thing we have not
done is to consider the effect of different orderings.  We could, for example,
stub an ordering predicate LE and then axiomatize the needed properties over
some domain.  For the moment we are wary of giving up Acl2's built-in treatment
of < (i.e., linear rewrite rules).

This book is briefly described in the paper "Defthms about zip and tie", UTCS
tech report TR97-02.

To certify this book, you need to define the POWERLISTS package and then run
certify-book on this file.  Here's how I do it:

    (ld ;; newline to fool dependency scanner
      "defpkg.lisp")
    (certify-book "sort" 4)
    (in-package "POWERLISTS")

|#

(in-package "POWERLISTS")
(include-book "algebra")

(set-verify-guards-eagerness 2)

;; We begin by defining the domain over which we're interested in sorting.  We
;; restrict ourselves to numeric lists.

(defmacro numericp (x)
  `(acl2::real/rationalp ,x))
(defun p-number-list (x)
  "Check that powerlist x consists entirely of numbers"
  (if (powerlist-p x)
      (and (p-number-list (p-untie-l x))
	   (p-number-list (p-untie-r x)))
    (numericp x)))
(in-theory (disable (p-number-list)))

;; Next, we define what it means to be a sorted powerlist.  We do so by
;; defining the minimum and maximum elements of a powerlist.  A powerlist then
;; is sorted if it's either a singleton or the tie of two sorted powerlists
;; such that the maximum element of the left-hand side is not greater than the
;; minimum element of the right-hand side.

(defun p-min-elem (x)
  "Returns the minimum element of a powerlist"
  (if (powerlist-p x)
      (if (<= (p-min-elem (p-untie-l x))
	      (p-min-elem (p-untie-r x)))
	  (p-min-elem (p-untie-l x))
	(p-min-elem (p-untie-r x)))
    (realfix x)))
(in-theory (disable (p-min-elem)))

(defun p-max-elem (x)
  "Returns the maximum element of a powerlist"
  (if (powerlist-p x)
      (if (>= (p-max-elem (p-untie-l x)) (p-max-elem (p-untie-r x)))
	  (p-max-elem (p-untie-l x))
	(p-max-elem (p-untie-r x)))
    (realfix x)))
(in-theory (disable (p-max-elem)))

(defun p-sorted-p (x)
  "Predicate true iff the powerlist x is non-descending"
  (if (powerlist-p x)
      (and (p-sorted-p (p-untie-l x))
	   (p-sorted-p (p-untie-r x))
	   (<= (p-max-elem (p-untie-l x))
	       (p-min-elem (p-untie-r x))))
    t))
(in-theory (disable (p-sorted-p)))

;; Trivially, the minimum and maximum elements of a list of numbers are
;; numeric.

(defthm min-of-numbers-is-numeric
  (implies (p-number-list x)
	   (numericp (p-min-elem x)))
  :rule-classes :type-prescription)

(defthm max-of-numbers-is-numeric
  (implies (p-number-list x)
	   (numericp (p-max-elem x)))
  :rule-classes :type-prescription)

;; How to satisfy the constraing "for i in 1..n-1, A[i] <= A[i-1]" most
;; efficiently?  Why, with the loop "for i in 1..n A[i] = 0"!  To avoid such
;; silliness, we define a function to count the occurrences of an element in a
;; list.  We will further require that a sort function preserves this count.

(defun p-member-count (x m)
  "Return the number of times scalar m occurs in powerlist x"
  (if (powerlist-p x)
      (+ (p-member-count (p-untie-l x) m)
	 (p-member-count (p-untie-r x) m))
    (if (equal x m) 1 0)))
(in-theory (disable (p-member-count)))

;; Now, we can prove some theorems useful to all sorters.  For example, we can
;; reason about number-lists and zip.

(defthm zip-of-numbers-is-number-list
  (implies (and (p-number-list x)
		(p-number-list y))
	   (p-number-list (p-zip x y)))
  :hints (("Goal"
	   :use (:functional-instance zip-b-tie-list-of-type-fn
				      (b-tie-list-of-type-fn
				       p-number-list)
				      (type-fn (lambda (x) (numericp x)))))))

(defthm unzip-of-numbers-is-number-list
  (implies (and (powerlist-p x)
		(p-number-list x))
	   (and (p-number-list (p-unzip-l x))
		(p-number-list (p-unzip-r x))))
  :hints (("Goal"
	   :use (:functional-instance unzip-b-tie-list-of-type-fn
				      (b-tie-list-of-type-fn
				       p-number-list)
				      (type-fn (lambda (x) (numericp x))))))
  :rule-classes (:rewrite :forward-chaining))

;; We can also prove theorems about hos max/min-elem behave over zip/unzip

(defun fix-min (x y)
  (declare (xargs :guard (and (numericp x) (numericp y))))
  (let ((fx (realfix x))
	(fy (realfix y)))
    (if (< fy fx) fy fx)))
(defun fix-max (x y)
  (declare (xargs :guard (and (numericp x) (numericp y))))
  (let ((fx (realfix x))
	(fy (realfix y)))
    (if (< fy fx) fx fy)))
(defthm max-elem-zip
	   (equal (p-max-elem (p-zip x y))
		  (if (>= (p-max-elem x) (p-max-elem y))
		      (p-max-elem x)
		    (p-max-elem y)))
  :hints (("Goal"
	   :use (:functional-instance zip-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 p-max-elem)
				      (equiv equal)
				      (fn2-accum fix-max)
				      (fn1 realfix))
	   :in-theory (disable zip-b-tie-fn2-accum-fn1))))

(defthm min-elem-zip
  (equal (p-min-elem (p-zip x y))
	 (if (<= (p-min-elem x) (p-min-elem y))
	     (p-min-elem x)
	   (p-min-elem y)))
  :hints (("Goal"
	   :use (:functional-instance zip-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 p-min-elem)
				      (equiv equal)
				      (fn2-accum fix-min)
				      (fn1 realfix))
	   :in-theory (disable zip-b-tie-fn2-accum-fn1))))

(defthm min-elem-unzip
  (implies (powerlist-p x)
	   (and (>= (p-min-elem (p-unzip-l x))
		    (p-min-elem x))
		(>= (p-min-elem (p-unzip-r x))
		    (p-min-elem x))))
  :hints (("Goal"
	   :use (:functional-instance unzip-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 p-min-elem)
				      (equiv equal)
				      (fn2-accum fix-min)
				      (fn1 realfix))
	   :in-theory (disable zip-b-tie-fn2-accum-fn1)))
  :rule-classes (:rewrite :linear))


(defthm max-elem-unzip
  (implies (powerlist-p x)
	   (and (<= (p-max-elem (p-unzip-l x)) (p-max-elem x))
		(<= (p-max-elem (p-unzip-r x)) (p-max-elem x))))
  :hints (("Goal"
	   :use (:functional-instance unzip-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 p-max-elem)
				      (equiv equal)
				      (fn2-accum fix-max)
				      (fn1 realfix))
	   :in-theory (disable zip-b-tie-fn2-accum-fn1)))
  :rule-classes (:rewrite :linear))

;; Of course, this is a classic theorem about min/max elem

(defthm min-elem-<=-max-elem
  (<= (p-min-elem x) (p-max-elem x))
  :rule-classes (:rewrite :linear))

;; We can also reason about sort and unzip.  Sadly, sort and zip aren't as nice
;; as sort and tie.  Even more sadly, many fast (i.e., parallel) sorting
;; algorithms are based on zip.

(defthm sorted-unzip
  (implies (p-sorted-p x)
	   (and (p-sorted-p (p-unzip-l x)) (p-sorted-p (p-unzip-r x)))))


