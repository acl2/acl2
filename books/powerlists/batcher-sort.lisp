#|

This is in an ACL2 "book" defining a batcher-merge sort for powerlists.  It
uses the infrastructure defined in merge-sort.lisp.    This book, as well as
others working with powerlists, is described in the paper "Defthms About Zip
and Tie", UTCS tech report TR97-02.

The informal correctness algorithm is as follows.  Consider merging two sorted
lists X = (x1 x2 ... xn) and Y = (y1 y2 ... yn).  We restrict ourselves to
lists of length n=2^k for some k.  Now, the merging step is given by

    (merge '(x1 x2 ... xn) '(y1 y2 ... yn))
	=
    (zip (min (merge '(x1 x3 ... x{n-1}) '(y2 y4 ... yn))
	      (merge '(x2 x4 ... xn)     '(y1 y3 ... y{n-1})))
	 (max (merge '(x1 x3 ... x{n-1}) '(y2 y4 ... yn))
	      (merge '(x2 x4 ... xn)     '(y1 y3 ... y{n-1}))))

Ok, now let's break this up into two pieces.  Consider the step

    (zip (min A B) (max A B))

This is sorted when A and B have this remarkable property:  A and B are
said to be interleaved if for any valid indices i<j:

    (1) Ai <= Aj
    (2) Bi <= Bj
    (3) Ai <= Bj
    (4) Bi <= Aj

Conditions (1) and (2) guarantee that A and B are sorted.  The remaining
conditions guarantee that the Ak/Bk should appear after A{k-1}/B{k-1} and
before A{k+1}/B{k+1} in the sorted sequence.  That is, to find the correct
position for Ak/Bk, we need only decide which of these comes first and then
ensure thay they're both before A{k+1}/B{k+1} and after A{k-1}/B{k-1}.  And
this, of course, is precisely what (zip (min A B) (max A B)) does.  The first
two elements of this list are (min a1 b1) (max a1 b1).  These are then followed
by (min a2 b2) (max a2 b2) and so on.

So, our proof reduces to this fact.  Given that X and Y are sorted, the
following are interleaved:

    (a) (merge (unzip-l x) (unzip-r y))
    (b) (merge (unzip-r x) (unzip-l y))

Why should we believe this property?  Well, let X and Y be as above, and let's
say formula (a) is A = (a1 a2 ... an) and (b) is B = (b1 b2 ... bn).  Now,
consider a valid pair of indices i<j.  That ai <= aj and bi <= bj follows from
the fact that (a) and (b) are sorted (i.e., the induction hypothesis).  Also,
we know that the a's and b's are either x's or y's.  So, since the list (a)
contains the odd-indexed x's, and the list (b) the even-indexed x's, for any
index i, the a's up to i can not contain less x's than the b's up to i.  This
is because any fewer x's have to be made up with some y's, and these are
even-indexed y's, so that (b) can't contain more y's than (a) does.  It's a
seemingly circular argument, but the base case is clear, and the rest follows.

So, together with the previous claim, this shows that merge does, indeed
generate a sorted powerlist when its inputs are sorted.

To certify this book, you need to define the POWERLISTS package and then run
certify-book on this file.  Here's how I do it:

    (ld ;; newline to fool dependency scanner
      "defpkg.lisp")
    (certify-book "batcher-sort" 4)
    (in-package "POWERLISTS")

|#

(in-package "POWERLISTS")
(include-book "merge-sort")
(include-book "arithmetic/top" :dir :system :load-compiled-file nil)

(set-verify-guards-eagerness 2)

;;; We now define the batcher-merge function itself.  We begin with the
;;; definition of p-min and p-max, which simply return a powerlist composed of
;;; the pairwise minimum (maximum) elements from two powerlists.

(defun p-min (x y)
  "Returns a powerlist with the pairwise minimum elements of x and y"
  (declare (xargs :guard (and (p-similar-p x y)
			      (p-number-list x)
			      (p-number-list y))))
  (if (and (powerlist-p x) (powerlist-p y))
      (p-zip (p-min (p-unzip-l x) (p-unzip-l y))
	     (p-min (p-unzip-r x) (p-unzip-r y)))
    (fix-min x y)))

(defun p-max (x y)
  "Returns a powerlist with the pairwise maximum elements of x and y"
  (declare (xargs :guard (and (p-similar-p x y)
			      (p-number-list x)
			      (p-number-list y))))
  (if (and (powerlist-p x) (powerlist-p y))
      (p-zip (p-max (p-unzip-l x) (p-unzip-l y))
	     (p-max (p-unzip-r x) (p-unzip-r y)))
    (fix-max x y)))

;;; This is batcher-merge function proper.  Note how the recursive calls to
;;; batcher-merge "swap" the left and right unzips of x and y.  Because of this
;;; swap, batcher-merge is only useful for regular lists x, y.  This is
;;; because x and y should be similar, and then we we would want the left-unzip
;;; of x to be similar to the right-unzip of y, etc.

(defun p-batcher-merge (x y)
  "Merge two sorted powerlists"
  (declare (xargs :guard (and (p-regular-p x)
			      (p-similar-p x y)
			      (p-number-list x)
			      (p-number-list y))
		  :verify-guards nil))
  (if (powerlist-p x)
      (p-zip (p-min (p-batcher-merge (p-unzip-l x)
				     (p-unzip-r y))
		    (p-batcher-merge (p-unzip-r x)
				     (p-unzip-l y)))
	     (p-max (p-batcher-merge (p-unzip-l x)
				     (p-unzip-r y))
		    (p-batcher-merge (p-unzip-r x)
				     (p-unzip-l y))))
    (p-zip (p-min x y) (p-max x y))))

;;; This is the driver routine that uses batcher-merge to sort a powerlist.

(defun p-batcher-sort (x)
  "Sort a powerlist"
  (declare (xargs :guard (and (p-regular-p x)
			      (p-number-list x))
		  :verify-guards nil))
  (if (powerlist-p x)
      (p-batcher-merge (p-batcher-sort (p-untie-l x))
		       (p-batcher-sort (p-untie-r x)))
    x))

;;; The definitions below use tie instead of zip.  They're more convenient in
;;; certain proofs.

(defun p-min-tie (x y)
  "Returns a powerlist with the pairwise minimum elements of x and y"
  (declare (xargs :guard (and (p-similar-p x y)
			      (p-number-list x)
			      (p-number-list y))))
  (if (and (powerlist-p x) (powerlist-p y))
      (p-tie (p-min-tie (p-untie-l x) (p-untie-l y))
	     (p-min-tie (p-untie-r x) (p-untie-r y)))
    (fix-min x y)))

(defun p-max-tie (x y)
  "Returns a powerlist with the pairwise maximum elements of x and y"
  (declare (xargs :guard (and (p-similar-p x y)
			      (p-number-list x)
			      (p-number-list y))))
  (if (and (powerlist-p x) (powerlist-p y))
      (p-tie (p-max-tie (p-untie-l x) (p-untie-l y))
	     (p-max-tie (p-untie-r x) (p-untie-r y)))
    (fix-max x y)))

;;; We show that these definitions are equivalent to their zip counterparts.
;;; The proof follows from the generic proof in algebra.lisp

(defthm min-tie-same-as-min-zip
  (implies (p-similar-p x y)
	   (equal (p-min x y) (p-min-tie x y)))
  :hints (("Goal"
	   :by (:functional-instance b-tie-fn2-same-as-a-zip-fn2
				     (a-zip-fn2 p-min)
				     (b-tie-fn2 p-min-tie)
				     (fn2 fix-min))))
  :rule-classes nil)

(defthm max-tie-same-as-max-zip
  (implies (p-similar-p x y)
	   (equal (p-max x y) (p-max-tie x y)))
  :hints (("Goal"
	   :by (:functional-instance b-tie-fn2-same-as-a-zip-fn2
				     (a-zip-fn2 p-max)
				     (b-tie-fn2 p-max-tie)
				     (fn2 fix-max))))
  :rule-classes nil)

;;; We are driving towards the proof that batcher-merge generates a list of
;;; numbers if its inputs are lists of numbers.  First, we show that zip
;;; and unzip preserve lists of numbers, using the generic results proved in
;;; algebra.lisp.

(defthm p-min-of-numbers-is-number-list
  (p-number-list (p-min x y))
  :rule-classes (:rewrite :type-prescription))

(defthm p-max-of-numbers-is-number-list
  (p-number-list (p-max x y))
  :rule-classes (:rewrite :type-prescription))

(defthm p-min-tie-of-numbers-is-number-list
  (p-number-list (p-min-tie x y))
  :rule-classes (:rewrite :type-prescription))

(defthm p-max-tie-of-numbers-is-number-list
  (p-number-list (p-max-tie x y))
  :rule-classes (:rewrite :type-prescription))

;;; The similarity property is, perhaps, the single most important property of
;;; two powerlists.   The following theorems allow us to reason about the
;;; similarity of min/max powerlists.  All these theorems are merely instances
;;; of meta-theorems proved in algebra.lisp.

(defthm min-similar-1
  (implies (p-similar-p x y)
	   (p-similar-p (p-min x y) x))
  :hints (("Goal"
	   :by (:functional-instance a-zip-fn2-similar-1
				     (a-zip-fn2 p-min)
				     (fn2 fix-min)))))

(defthm min-tie-similar-1
  (implies (p-similar-p x y)
	   (p-similar-p (p-min-tie x y) x))
  :hints (("Goal"
	   :by (:functional-instance b-tie-fn2-similar-1
				     (b-tie-fn2 p-min-tie)
				     (fn2 fix-min)))))

(defthm max-similar-1
  (implies (p-similar-p x y)
	   (p-similar-p (p-max x y) x))
  :hints (("Goal"
	   :by (:functional-instance a-zip-fn2-similar-1
				     (a-zip-fn2 p-max)
				     (fn2 fix-max)))))

(defthm max-tie-similar-1
  (implies (p-similar-p x y)
	   (p-similar-p (p-max-tie x y) x))
  :hints (("Goal"
	   :by (:functional-instance b-tie-fn2-similar-1
				     (b-tie-fn2 p-max-tie)
				     (fn2 fix-max)))))

(defthm min-similar-2
  (implies (p-similar-p x y)
	   (p-similar-p (p-min x y) y))
  :hints (("Goal"
	   :by (:functional-instance a-zip-fn2-similar-2
				     (a-zip-fn2 p-min)
				     (fn2 fix-min)))))

(defthm min-tie-similar-2
  (implies (p-similar-p x y)
	   (p-similar-p (p-min-tie x y) y))
  :hints (("Goal"
	   :by (:functional-instance b-tie-fn2-similar-2
				     (b-tie-fn2 p-min-tie)
				     (fn2 fix-min)))))

(defthm max-similar-2
  (implies (p-similar-p x y)
	   (p-similar-p (p-max x y) y))
  :hints (("Goal"
	   :by (:functional-instance a-zip-fn2-similar-2
				     (a-zip-fn2 p-max)
				     (fn2 fix-max)))))

(defthm max-tie-similar-2
  (implies (p-similar-p x y)
	   (p-similar-p (p-max-tie x y) y))
  :hints (("Goal"
	   :by (:functional-instance b-tie-fn2-similar-2
				     (b-tie-fn2 p-max-tie)
				     (fn2 fix-max)))))

(defthm min-max-similar
  (implies (p-similar-p x y)
	   (p-similar-p (p-min x y) (p-max x y))))

(defthm min-max-tie-similar
  (implies (p-similar-p x y)
	   (p-similar-p (p-min-tie x y) (p-max-tie x y))))

;;; We now have enough machinery to characterize the structure of a tree
;;; returned by batcher-merge.  It basically looks like the zip/tie of the two
;;; input arguments together, which should be regular and similar, so
;;; batcher-merge will be a regular list.  It turns out that proving this for
;;; zip is sufficient.

(defthm merge-similar-zip
  (implies (and (p-regular-p x)
                (p-similar-p x y))
           (p-similar-p (p-batcher-merge x y) (p-zip x y)))
  :hints (("Goal"
           :induct (unzip-swap-on-x-and-y x y)
           :do-not '(eliminate-destructors)))
  :rule-classes nil)

;;; A more useful structure lemma is the following, which says that the results
;;; from the two recursive calls of batcher-merge will be similar.  This is
;;; simply a corollary of the above.

(defthm merge-regular-swap-unzips
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-similar-p x y))
	   (p-similar-p (p-batcher-merge (p-unzip-l x) (p-unzip-r y))
			(p-batcher-merge (p-unzip-r x) (p-unzip-l y))))
  :hints (("Goal"
	   :use ((:instance merge-similar-zip
			    (x (p-unzip-l x))
			    (y (p-unzip-r y)))
		 (:instance merge-similar-zip
			    (x (p-unzip-r x))
			    (y (p-unzip-l y)))))))


;;; And finally, we have the first proof obligation of merge, namely that it
;;; produces a powerlist of numbers.

(defthm merge-of-numbers-is-number-list
  (p-number-list (p-batcher-merge x y))
  :rule-classes (:rewrite :type-prescription))

;;; We are now driving towards the result that batcher-merge preserves the
;;; number of occurrences of each element.  We start by proving the equivalent
;;; results for zip/unzip.  We need these proofs here, because the generic
;;; definitions were built in terms of tie/untie instead.  Of course, it is an
;;; easy consequence (ha!) of the associativity/commutativity that any such
;;; accumulator is the same whether defined using unzip or untie.

(defthm a-zip-plus-fn1-of-min-max
  (implies (and (p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (equal (+ (a-zip-plus-fn1 (p-max x y))
		     (a-zip-plus-fn1 (p-min x y)))
		  (+ (a-zip-plus-fn1 x)
		     (a-zip-plus-fn1 y)))))

(defthm a-zip-plus-fn1-of-merge
  (implies (and (p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (equal (a-zip-plus-fn1 (p-batcher-merge x y))
		  (+ (a-zip-plus-fn1 x)
		     (a-zip-plus-fn1 y))))
  :hints (("Subgoal *1/25"
	   :use (:instance merge-regular-swap-unzips)
	   :in-theory (disable merge-regular-swap-unzips))))

(defthm b-tie-plus-fn1-of-merge
  (implies (and (p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (equal (b-tie-plus-fn1 (p-batcher-merge x y))
		  (+ (b-tie-plus-fn1 x)
		     (b-tie-plus-fn1 y))))
  :hints (("Goal"
	   :use ((:instance a-zip-plus-fn1-same-as-b-tie-plus-fn1)
		 (:instance a-zip-plus-fn1-same-as-b-tie-plus-fn1 (x y))
		 (:instance a-zip-plus-fn1-same-as-b-tie-plus-fn1
			    (x (p-batcher-merge x y)))))))


;;; Now that we've proved all the special cases, we can fulfill the proof
;;; obligation that batcher-merge preserves the member-count of its arguments.

(defthm member-count-of-merge
  (implies (and (p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (equal (p-member-count
		   (p-batcher-merge x y) m)
		  (+ (p-member-count x m)
		     (p-member-count y m))))
  :hints (("Goal"
	   :by (:functional-instance b-tie-plus-fn1-of-merge
				     (b-tie-plus-fn1 (lambda (x)
						       (p-member-count x m)))
				     (fn1-num (lambda (x)
						(if (= x m) 1 0)))))))

;;; Finally, we're ready to drive towards the Big Theorem, that batcher-merge
;;; correctly merges sorted lists.  We start out by defining the interleaved
;;; property, which is described in the commentary at the top of the
;;; file. We're driving towards the first of the two parts of the Big Theorem.
;;; The first is that if the two recursive calls of batcher-merge return lists
;;; that are interleaved (i.e., a powerlists whose ith element is randomly
;;; selected from the ith elements of X and Y is sorted), then batcher-merge
;;; sorts properly.  The second part, of course, is that the two recursive
;;; calls behave as promised.

(defun p-interleaved-p (x y)
  "Check to see if two lists are interleaved (i.e., jointly sorted)"
  (declare (xargs :guard (and (p-number-list x)
			      (p-number-list y))))
  (if (powerlist-p x)
      (and (powerlist-p y)
	   (p-interleaved-p (p-untie-l x) (p-untie-l y))
	   (p-interleaved-p (p-untie-r x) (p-untie-r y))
	   (<= (p-max-elem (p-untie-l x))
	       (p-min-elem (p-untie-r x)))
	   (<= (p-max-elem (p-untie-l x))
	       (p-min-elem (p-untie-r y)))
	   (<= (p-max-elem (p-untie-l y))
	       (p-min-elem (p-untie-r x)))
	   (<= (p-max-elem (p-untie-l y))
	       (p-min-elem (p-untie-r y))))
    (not (powerlist-p y))))

;;; We need to build some powerful machinery to reason about interleaved
;;; powerlists.  We start by specifying how the max/min elements of a
;;; powerlists are affected by zip/unzip and also by tie/untie.

(defthm min-elem-p-min-tie
  (implies (p-similar-p x y)
	   (equal (p-min-elem (p-min-tie x y))
		  (if (<= (p-min-elem x) (p-min-elem y))
		      (p-min-elem x)
		    (p-min-elem y)))))

(defthm min-elem-p-min
  (implies (p-similar-p x y)
	   (equal (p-min-elem (p-min x y))
		  (if (<= (p-min-elem x) (p-min-elem y))
		      (p-min-elem x)
		    (p-min-elem y))))
  :hints (("Goal" :use ((:instance min-tie-same-as-min-zip)
			(:instance min-elem-p-min-tie)))))

(defthm max-elem-p-min-tie
  (implies (p-similar-p x y)
	   (and (<= (p-max-elem (p-min-tie x y))
		    (p-max-elem x))
		(<= (p-max-elem (p-min-tie x y))
		    (p-max-elem y))))
  :rule-classes (:rewrite :linear))

(defthm max-elem-p-min
  (implies (p-similar-p x y)
	   (and (<= (p-max-elem (p-min x y))
		    (p-max-elem x))
		(<= (p-max-elem (p-min x y))
		    (p-max-elem y))))
  :hints (("Goal" :use ((:instance min-tie-same-as-min-zip)
			(:instance max-elem-p-min-tie))))
  :rule-classes (:rewrite :linear))

(defthm min-elem-p-max-tie
  (implies (p-similar-p x y)
	   (and (>= (p-min-elem (p-max-tie x y))
		    (p-min-elem x))
		(>= (p-min-elem (p-max-tie x y))
		    (p-min-elem y))))
  :rule-classes (:rewrite :linear))

(defthm min-elem-p-max
  (implies (p-similar-p x y)
	   (and (>= (p-min-elem (p-max x y))
		    (p-min-elem x))
		(>= (p-min-elem (p-max x y))
		    (p-min-elem y))))
  :hints (("Goal" :use ((:instance max-tie-same-as-max-zip)
			(:instance min-elem-p-max-tie))))
  :rule-classes (:rewrite :linear))


(defthm max-elem-p-max-tie
  (implies (p-similar-p x y)
	   (equal (p-max-elem (p-max-tie x y))
		  (if (>= (p-max-elem x) (p-max-elem y))
		      (p-max-elem x)
		    (p-max-elem y)))))

(defthm max-elem-p-max
  (implies (p-similar-p x y)
	   (equal (p-max-elem (p-max x y))
		  (if (>= (p-max-elem x) (p-max-elem y))
		      (p-max-elem x)
		    (p-max-elem y))))
  :hints (("Goal" :use ((:instance max-tie-same-as-max-zip)
			(:instance max-elem-p-max-tie)))))

;;; Now, we derive two easy consequences of the interleaved definition.
;;; Namely, the two lists must themselves be sorted.

(defthm interleaved-implies-sorted-1
  (implies (p-interleaved-p x y)
	   (p-sorted-p x))
  :rule-classes (:type-prescription :rewrite))

(defthm interleaved-implies-sorted-2
  (implies (p-interleaved-p x y)
	   (p-sorted-p y))
  :rule-classes (:type-prescription :rewrite))

;;; Even better, we can conclude that two interleaved powerlists are
;;; similar. This turns out to be a dangerous rewrite rule, so we disable it.

(defthm interleaved-implies-similar
  (implies (p-interleaved-p x y)
	   (equal (p-similar-p x y) t))
  :rule-classes nil)

;;; It is tempting to believe that interleaved is an equivalence
;;; relation. Certainly, the theorems below indicate that.  However, it's
;;; simply not true, since the missing theorem (reflexivity) is clearly false.
;;; We don't know if ACL2 can make as much use of the following as it does out
;;; of equivalence reasoning.

(defthm p-interleaved-p-is-boolean
  (booleanp (p-interleaved-p x y)))

(defthm p-interleaved-p-is-symmetric
  (implies (p-interleaved-p x y)
	   (p-interleaved-p y x)))

(defthm p-interleaved-p-is-transitive
  (implies (and (p-interleaved-p x y)
		(p-interleaved-p y z))
	   (p-interleaved-p x x)))

;;; Now, we can prove that (zip (min A B) (max A B)), the last step of
;;; batcher-merge properly sorts if A and B are interleaved.  It turns out to
;;; be much easier to prove this is we allow ourselves to use the untie
;;; versions of the min/max functions.  So we do so first, then prove the main
;;; result by invoking their equality.

(defthm zip-min-max-sorted-if-interleaved-tie
  (implies (and (p-interleaved-p x y)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (p-sorted-p (p-zip (p-min-tie x y) (p-max-tie x y)))))

(defthm zip-min-max-sorted-if-interleaved
  (implies (and (p-interleaved-p x y)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (p-sorted-p (p-zip (p-min x y)
			      (p-max x y))))
  :hints (("Goal"
	   :use ((:instance min-tie-same-as-min-zip)
		 (:instance max-tie-same-as-max-zip)
		 (:instance zip-min-max-sorted-if-interleaved-tie))
	   :in-theory (disable zip-min-max-sorted-if-interleaved-tie))))

;;; We are now trying to prove that the recursive calls to batcher merge return
;;; interleaved results.  The proof (outlined at the top of the file, and
;;; detailed in the tech report UTCS TR97-02) is based on reasoning about
;;; indices.  In particular, it can be proved by considering which X's and Y's
;;; can appear in corresponding prefixes of the two merged lists.  We replace
;;; the notion of indices with the (equivalent) notion of the number of
;;; elements smaller than a given X.  We say "equivalent", since the sublists
;;; are expected to be sorted.  (Of course, there's duplicates to worry about,
;;; but it turns out that's not a problem.)

;;; First, we define the concepts of p-member-count-<= and then we prove lemmas
;;; that allow us to compute this across the function symbols we already know.

(defun p-member-count-<= (x m)
  "Return the number of times a scalar <= m occurs in powerlist x"
  (declare (xargs :guard (and (p-number-list x) (numericp m))))
  (if (powerlist-p x)
      (+ (p-member-count-<= (p-untie-l x) m)
	 (p-member-count-<= (p-untie-r x) m))
    (if (<= (realfix x) m) 1 0)))

(defun p-elem-count (x)
  "Return the number of scalars in powerlist x"
  (declare (xargs :guard (p-number-list x)))
  (if (powerlist-p x)
      (+ (p-elem-count (p-untie-l x))
	 (p-elem-count (p-untie-r x)))
    1))

(defthm similar-elem-count
  (implies (and (p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context
                ;; (avoids rewrite stack overflow in
                ;; unzip-of-sorted-is-interleaved):
                (syntaxp (not (acl2::term-order x y))))
	   (equal (p-elem-count x) (p-elem-count y))))

(defthm max-elem-member-count-<=
  (implies (<= (p-max-elem x) m)
	   (equal (p-member-count-<= x m) (p-elem-count x))))

(defthm min-elem-member-count-<=
  (implies (< m (p-min-elem x))
	   (equal (p-member-count-<= x m) 0)))

(defthm min-elem-member-count-<=-2
  (implies (>= m (p-min-elem x))
	   (<= 1 (p-member-count-<= x m)))
  :rule-classes (:rewrite :linear))

(defthm max-elem-member-count-<=-2
  (implies (< m (p-max-elem x))
	   (< (p-member-count-<= x m) (p-elem-count x)))
  :rule-classes (:rewrite :linear))

(defthm sorted-member-count-<=-p-min-untie-r
  (implies (and (powerlist-p x)
		(p-sorted-p x))
	   (<= (p-elem-count (p-untie-l x))
	       (p-member-count-<= x (p-min-elem (p-untie-r x)))))
  :rule-classes (:rewrite :linear))

(defthm sorted-member-count-<=-p-max-untie-l
  (implies (and (powerlist-p x)
		(p-sorted-p x))
	   (<= (p-elem-count (p-untie-l x))
	       (p-member-count-<= x (p-max-elem (p-untie-l x)))))
  :rule-classes (:rewrite :linear))

;;; The next set of theorems are key.  They tell us how the elements of a
;;; sorted list are distributed when we take their unzip.  This is the theorem
;;; that will let us argue about how many X's and Y's can go at the front of
;;; the merged sublists, and so will eventually prove the two merged sublists
;;; are interleaved.

(defthm member-count-<=-of-sorted-unzips-1
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-sorted-p x))
	   (<= (p-member-count-<= (p-unzip-r x) m)
	       (p-member-count-<= (p-unzip-l x) m)))
  :rule-classes (:rewrite :linear))

(defthm member-count-<=-of-interleaved-crossing-rule
  (implies (and (p-interleaved-p x y)
		(< (p-member-count-<= x m)
		   (p-member-count-<= y m)))
	   (< m (p-max-elem x)))
  :rule-classes (:rewrite :linear))

(defthm member-count-<=-of-interleaved-crosses-once
  (implies (and (powerlist-p x)
		(p-interleaved-p x y)
		(< (p-member-count-<= (p-untie-l x) m)
		   (p-member-count-<= (p-untie-l y) m)))
	   (equal (equal (p-member-count-<= (p-untie-r x) m)
			 (p-member-count-<= (p-untie-r y) m))
		  t))
  :hints (("Goal"
	   :use (:instance member-count-<=-of-interleaved-crossing-rule
			   (x (p-untie-l x))
			   (y (p-untie-l y)))
	   :in-theory (disable member-count-<=-of-interleaved-crossing-rule))))

(defthm member-count-<=-of-interleaved-1
  (implies (and (powerlist-p x)
		(p-interleaved-p x y)
		(equal (1+ (p-member-count-<= (p-untie-l x) m))
		       (p-member-count-<= (p-untie-l y) m)))
	   (equal (equal (p-member-count-<= (p-untie-r x) m)
			 (p-member-count-<= (p-untie-r y) m))
		  t))
  :hints (("Goal"
	   :use (:instance member-count-<=-of-interleaved-crosses-once)
	   :in-theory (disable member-count-<=-of-interleaved-crosses-once))))

(defthm member-count-<=-of-interleaved-2
  (implies (and (powerlist-p x)
		(p-interleaved-p x y)
		(equal (1+ (p-member-count-<= (p-untie-l x) m))
		       (p-member-count-<= (p-untie-l y) m)))
	   (and (equal (equal (1+ (p-member-count-<= (p-untie-r x) m))
			      (p-member-count-<= (p-untie-r y) m))
		       nil)
		(equal (equal (1+ (p-member-count-<= (p-untie-r y) m))
			      (p-member-count-<= (p-untie-r x) m))
		       nil)))
  :hints (("Goal"
	   :use (:instance member-count-<=-of-interleaved-1)
	   :in-theory (disable member-count-<=-of-interleaved-1
			       member-count-<=-of-interleaved-crosses-once))))

(defthm member-count-<=-of-interleaved
  (implies (p-interleaved-p x y)
	   (or (equal (p-member-count-<= x m) (p-member-count-<= y m))
	       (equal (1+ (p-member-count-<= y m)) (p-member-count-<= x m))
	       (equal (1+ (p-member-count-<= x m)) (p-member-count-<= y m))))
  :rule-classes nil)

(defthm unzip-of-sorted-is-interleaved
  (implies (and (p-sorted-p x)
		(p-regular-p x))
	   (p-interleaved-p (p-unzip-l x)  (p-unzip-r x))))

(defthm member-count-<=-of-sorted-unzips-2
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-sorted-p x))
	   (<= (p-member-count-<= (p-unzip-l x) m)
	       (1+ (p-member-count-<= (p-unzip-r x)
				      m))))
  :hints (("Goal"
	   :use ((:instance unzip-of-sorted-is-interleaved)
		 (:instance member-count-<=-of-interleaved
			    (x (p-unzip-l x)) (y (p-unzip-r x)))
		 (:instance member-count-<=-of-sorted-unzips-1))
	   :in-theory (disable unzip-of-sorted-is-interleaved
			       member-count-<=-of-sorted-unzips-1)))
  :rule-classes (:rewrite :linear))

(defthm member-count-<=-of-merge
  (implies (and (p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y))
	   (equal (p-member-count-<=
		   (p-batcher-merge x y)
		   m)
		  (+ (p-member-count-<= x m)
		     (p-member-count-<= y m))))
  :hints (("Goal"
	   :by (:functional-instance b-tie-plus-fn1-of-merge
				     (b-tie-plus-fn1
				      (lambda (x) (p-member-count-<= x m)))
				     (fn1-num
				      (lambda (x) (if (<= (realfix x) m)
						      1 0)))))))

;;; The key theorem.  We now know that the member-counts (i.e., indices) of any
;;; given number in the two sublists regurned by batcher merge must be within
;;; 1.  What is left is to show that this fact implies the two sublists are
;;; interleaved

(defthm member-count-<=-of-merge-unzips
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y)
		(p-sorted-p x)
		(p-sorted-p y))
	   (let ((M1 (p-member-count-<= (p-batcher-merge
					 (p-unzip-l x)
					 (p-unzip-r y))
					m))
		 (M2 (p-member-count-<= (p-batcher-merge
					 (p-unzip-r x)
					 (p-unzip-l y))
					m)))
	     (or (equal M1 M2)
		 (equal (1+ M1) M2)
		 (equal (1+ M2) M1))))
  :hints (("Goal"
	   :use ((:instance member-count-<=-of-sorted-unzips-1)
		 (:instance member-count-<=-of-sorted-unzips-1 (x y))
		 (:instance member-count-<=-of-sorted-unzips-2)
		 (:instance member-count-<=-of-sorted-unzips-2 (x y)))
	   :in-theory (disable member-count-<=-of-sorted-unzips-1
			       member-count-<=-of-sorted-unzips-2)))
  :rule-classes nil)

;;; Now, we prove, by contradiction, that the previous theorem implies the two
;;; sublists are interleaved.  We will do this by assuming that the sublists
;;; are not interleaved.  Then, we will find a specific number m, so that it
;;; violates the theorem above.  The function which picks this number is
;;; defined below.

(defun interleaved-p-cutoff (x y)
  "Counter-example to member-count-<=-of-merge-unzips"
  (declare (xargs :guard (and (p-number-list x)
			      (p-number-list y))))
  (if (and (powerlist-p x) (powerlist-p y))
      (cond ((< (p-min-elem (p-untie-r x))
		(p-max-elem (p-untie-l x)))
	     (p-min-elem (p-untie-r x)))
	    ((< (p-min-elem (p-untie-r x))
		(p-max-elem (p-untie-l y)))
	     (p-min-elem (p-untie-r x)))
	    ((interleaved-p-cutoff (p-untie-l x)
				   (p-untie-l y))
	     (interleaved-p-cutoff (p-untie-l x)
				   (p-untie-l y)))
	    ((interleaved-p-cutoff (p-untie-r x)
				   (p-untie-r y))
	     (interleaved-p-cutoff (p-untie-r x)
				   (p-untie-r y))))
    nil))

(defthm interleaved-p-if-nil-cutoff
      (implies (and (p-similar-p x y)
                    (p-number-list x)
                    (p-number-list y)
                    (not (numericp
                          (interleaved-p-cutoff x y)))
                    (not (numericp
                          (interleaved-p-cutoff y x))))
               (p-interleaved-p x y)))

(encapsulate
 ()

 (local
  (defthm foo-1
    (implies (interleaved-p-cutoff x y)
	     (and (<= (p-min-elem x) (interleaved-p-cutoff x y))
		  (<= (interleaved-p-cutoff x y) (p-max-elem x))))
    :hints (("Goal" :induct (interleaved-p-cutoff x y)))
    :rule-classes (:linear :rewrite)))

 (local
  (defthm foo-2
    (implies (and (p-sorted-p x)
		  (interleaved-p-cutoff x y))
	     (< (interleaved-p-cutoff x y) (p-max-elem y)))
    :hints (("Goal" :induct (interleaved-p-cutoff x y)))
    :rule-classes (:linear :rewrite)))

 (local
  (defthm foo-3
    (implies (and (powerlist-p x)
		  (powerlist-p y)
		  (p-sorted-p x)
		  (p-sorted-p y)
		  (interleaved-p-cutoff (p-untie-l x) (p-untie-l y)))
	     (and (<= (interleaved-p-cutoff (p-untie-l x) (p-untie-l y))
		      (p-min-elem (p-untie-r x)))
		  (< (interleaved-p-cutoff (p-untie-l x) (p-untie-l y))
		     (p-min-elem (p-untie-r y)))))
    :rule-classes (:linear :rewrite)))

 (defthm member-count-diff-2-if-interleaved-cutoff-sorted
   (implies (and (p-similar-p x y)
		 (p-number-list x)
		 (p-number-list y)
		 (p-sorted-p x)
		 (p-sorted-p y)
		 (interleaved-p-cutoff x y))
	    (< (1+ (p-member-count-<=
		    y
		    (interleaved-p-cutoff x y)))
	       (p-member-count-<=
		x
		(interleaved-p-cutoff x y))))
   :hints (("Goal" :induct (interleaved-p-cutoff x y))
	   ("Subgoal *1/2'''"
	    :expand ((p-member-count-<= y (p-min-elem (powerlist-cdr x))))
	    :do-not '(eliminate-destructors)))
   :rule-classes nil))

;;; With the two theorems above, it is time to show that the inner calls to
;;; batcher merge are indeed interleaved.

(encapsulate
 ()

 (local
  (defthm inner-batcher-merge-call-is-interleaved-p-1
    (implies (and (powerlist-p x)
		  (p-regular-p x)
		  (p-similar-p x y)
		  (p-number-list x)
		  (p-number-list y)
		  (p-sorted-p x)
		  (p-sorted-p y)
		  (p-sorted-p (p-batcher-merge (p-unzip-l x) (p-unzip-r y)))
		  (p-sorted-p (p-batcher-merge (p-unzip-r x) (p-unzip-l y))))
	     (not (interleaved-p-cutoff (p-batcher-merge (p-unzip-l x)
							 (p-unzip-r y))
					(p-batcher-merge (p-unzip-r x)
							 (p-unzip-l y)))))
    :hints (("Goal"
	     :use ((:instance member-count-diff-2-if-interleaved-cutoff-sorted
			      (x (p-batcher-merge (p-unzip-l x) (p-unzip-r y)))
			      (y (p-batcher-merge (p-unzip-r x) (p-unzip-l y))))
		   (:instance member-count-<=-of-merge-unzips
			      (m (interleaved-p-cutoff
				  (p-batcher-merge (p-unzip-l x) (p-unzip-r y))
				  (p-batcher-merge (p-unzip-r x)
						   (p-unzip-l y))))))))))
 (local
  (defthm inner-batcher-merge-call-is-interleaved-p-2
    (implies (and (powerlist-p x)
		  (p-regular-p x)
		  (p-similar-p x y)
		  (p-number-list x)
		  (p-number-list y)
		  (p-sorted-p x)
		  (p-sorted-p y)
		  (p-sorted-p (p-batcher-merge (p-unzip-l x) (p-unzip-r y)))
		  (p-sorted-p (p-batcher-merge (p-unzip-r x) (p-unzip-l y))))
	     (not (interleaved-p-cutoff (p-batcher-merge (p-unzip-r x)
							 (p-unzip-l y))
					(p-batcher-merge (p-unzip-l x)
							 (p-unzip-r y)))))
    :hints (("Goal"
	     :use ((:instance member-count-diff-2-if-interleaved-cutoff-sorted
			      (x (p-batcher-merge (p-unzip-r x) (p-unzip-l y)))
			      (y (p-batcher-merge (p-unzip-l x) (p-unzip-r y))))
		   (:instance member-count-<=-of-merge-unzips
			      (m (interleaved-p-cutoff
				  (p-batcher-merge (p-unzip-r x) (p-unzip-l y))
				  (p-batcher-merge (p-unzip-l x)
						   (p-unzip-r y))))))))))

 (defthm inner-batcher-merge-call-is-interleaved-p
   (implies (and (powerlist-p x)
		 (p-regular-p x)
		 (p-similar-p x y)
		 (p-number-list x)
		 (p-number-list y)
		 (p-sorted-p x)
		 (p-sorted-p y)
		 (p-sorted-p
		  (p-batcher-merge (p-unzip-l x)
				   (p-unzip-r y)))
		 (p-sorted-p
		  (p-batcher-merge (p-unzip-r x)
				   (p-unzip-l y))))
	    (p-interleaved-p
	     (p-batcher-merge (p-unzip-l x)
			      (p-unzip-r y))
	     (p-batcher-merge (p-unzip-r x)
			      (p-unzip-l y))))
   :hints (("Goal"
	    :use ((:instance interleaved-p-if-nil-cutoff
			     (x (p-batcher-merge (p-unzip-l x) (p-unzip-r y)))
			     (y (p-batcher-merge (p-unzip-r x) (p-unzip-l y)))))
	    :in-theory (disable interleaved-p-if-nil-cutoff)))))

;;; Now, it is a simple matter to show that batcher merge returns a sorted
;;; list, as long as we assume the inner calls are doing their job.  I.e., we
;;; can now prove the inductive case of the proof

(defthm recursive-batcher-merge-is-sorted
  (implies (and (powerlist-p x)
		(p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y)
		(p-sorted-p x)
		(p-sorted-p y)
		(p-sorted-p
		 (p-batcher-merge (p-unzip-l x)
				  (p-unzip-r y)))
		(p-sorted-p
		 (p-batcher-merge (p-unzip-r x)
				  (p-unzip-l y))))
	   (p-sorted-p (p-batcher-merge x y)))
  :hints (("Goal"
	   :use ((:instance inner-batcher-merge-call-is-interleaved-p)
		 (:instance zip-min-max-sorted-if-interleaved
			    (x (p-batcher-merge (p-unzip-l x) (p-unzip-r y)))
			    (y (p-batcher-merge (p-unzip-r x) (p-unzip-l y)))))
	   :in-theory (disable inner-batcher-merge-call-is-interleaved-p
			       zip-min-max-sorted-if-interleaved))))

;;; This trivializes the following correctness result for batcher merge.

(defthm sorted-merge
  (implies (and (p-regular-p x)
		(p-similar-p x y)
		(p-number-list x)
		(p-number-list y)
		(p-sorted-p x)
		(p-sorted-p y))
	   (p-sorted-p (p-batcher-merge x y)))
  :hints (("Goal" :induct (unzip-swap-on-x-and-y x y))
	  ("Subgoal *1/1" :hands-off (p-batcher-merge))))

;;; We need only show the remaining proof obligations to invoke the generic
;;; merge sorting theorems

(defthm batcher-sort-similar
  (implies (p-regular-p x)
	   (p-similar-p (p-batcher-sort x) x))
  :hints (("Subgoal *1/2'"
	   :use (:instance merge-similar-zip
			   (x (p-batcher-sort (p-untie-l x)))
			   (y (p-batcher-sort (p-untie-r x)))))))

(defthm batcher-sort-regular
  (implies (p-regular-p x)
	   (p-regular-p (p-batcher-sort x)))
  :hints (("Goal"
	   :use (:instance batcher-sort-similar)
	   :in-theory (disable batcher-sort-similar))))

(defthm batcher-sort-number-list
  (implies (and (p-regular-p x)
		(p-number-list x))
	   (p-number-list (p-batcher-sort x))))

(defthm batcher-sort-is-permutation
  (implies (and (p-regular-p x)
		(p-number-list x))
	   (equal (p-member-count (p-batcher-sort x) m)
		  (p-member-count x m)))
  :hints (("Goal"
	   :by (:functional-instance merge-sort-is-permutation
				     (p-sortable-p (lambda (x)
						     (and (p-regular-p x)
							  (p-number-list x))))
				     (p-mergeable-p (lambda (x y)
						      (and (p-regular-p x)
							   (p-similar-p x y)
							   (p-number-list x)
							   (p-number-list y))))
				     (p-split-1 (lambda (x) (p-untie-l x)))
				     (p-split-2 (lambda (x) (p-untie-r x)))
				     (p-merge p-batcher-merge)
				     (p-merge-sort p-batcher-sort)))))

;;; And finally, we can invoke the result from the generic merge sort routine

(defthm batcher-sort-sorts-inputs
  (implies (and (p-regular-p x)
		(p-number-list x))
	   (p-sorted-p (p-batcher-sort x)))
  :hints (("Goal"
	   :by (:functional-instance merge-sort-sorts-input
				     (p-sortable-p (lambda (x)
						     (and (p-regular-p x)
							  (p-number-list x))))
				     (p-mergeable-p (lambda (x y)
						      (and (p-regular-p x)
							   (p-similar-p x y)
							   (p-number-list x)
							   (p-number-list y))))
				     (p-split-1 (lambda (x) (p-untie-l x)))
				     (p-split-2 (lambda (x) (p-untie-r x)))
				     (p-merge p-batcher-merge)
				     (p-merge-sort p-batcher-sort)))))

(verify-guards p-batcher-merge)
(verify-guards p-batcher-sort)
