#|

This is in an ACL2 "book" describing in general what it means to be a merge
sort.  It does this by introducing the stubbed functions split-1, split-2 and
merge that take a powerlist apart into two subpowerlists and merge two
sorted powerlists, respectively.  This book, as well as others working with
powerlists, is described in the paper "Defthms About Zip and Tie", UTCS tech
report TR97-02.

To certify this book, you need to define the POWERLISTS package and then run
certify-book on this file.  Here's how I do it:

    (ld ;; newline to fool dependency scanner
      "defpkg.lisp")
    (certify-book "merge-sort" 4)
    (in-package "POWERLISTS")

|#

(in-package "POWERLISTS")
(include-book "algebra")
(include-book "sort")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation ACL2::e0-ord-<)

(set-verify-guards-eagerness 2)

;;; We begin by stubbing out the split and merge functions, as well as the
;;; mergeable and sortable functions which specify when a merge can be applied
;;; to a given list (e.g., only numeric lists can be merged).  As part of the
;;; stubbing process, we have to demonstrate two functions that have the
;;; required properties.  That is, we have to prove the correctness of a
;;; merge sort algorithm.  It would have been possible to prove a trivial
;;; merge sort algorithm, e.g., one where no lists are mergeable, but this
;;; only became possible after the introduction of the "sortable" predicate.
;;; So instead, we define the algorithm "insertion merge".  As far as we know,
;;; it hasn't been studied in the literature, and with good reason, since it
;;; isn't particularly clever.

(encapsulate
 ((p-sortable-p (x) t)
  (p-mergeable-p (x y) t)
  (p-split-1 (x) t)
  (p-split-2 (x) t)
  (p-merge (x y) t)
  (p-merge-sort (x) x))

 ;; In general, we don't know what restrictions specific sorting algorithms
 ;; will place on lists.  At the very least, though, we expect the lists to be
 ;; composed of numbers.

 (local (defun p-sortable-p (x) (p-number-list x)))
 (local (defun p-mergeable-p (x y) (and (p-number-list x) (p-number-list y))))

 ;; The definition of the split functions is trivial.  We need only take the
 ;; left and right branches of the tree to fulfill the requirements.

 (local (defun p-split-1 (x) (declare (xargs :guard (powerlist-p x)))
	  (p-untie-l x)))
 (local (defun p-split-2 (x) (declare (xargs :guard (powerlist-p x)))
	  (p-untie-r x)))

 ;; The merge witnessing function is much more interesting.  We start out with
 ;; the auximilary function "insert" which adds an element into a sorted
 ;; powerlist.  Merge then, simply calls this insert routing repeatedly.
 ;; Notice the awkward recursion in the merge definition.  It made some of the
 ;; following proofs entertaining.

 ;; Note, by the way, that p-insert is NOT stubbed or exported.  It is merely
 ;; an artifact used inside this encapsulate to witness the function merge.

 (local (defun p-insert (e x)
	  (declare (xargs :guard (and (numericp e) (p-number-list x))))
	  (if (powerlist-p x)
	      (if (<= e (p-max-elem (p-untie-l x)))
		  (p-tie (p-insert e (p-untie-l x)) (p-untie-r x))
		(p-tie (p-untie-l x) (p-insert e (p-untie-r x))))
	    (if (<= e x)
		(p-tie e x)
	      (p-tie x e)))))
 (local (defun p-merge (x y)
	  (declare (xargs :guard (and (p-number-list x) (p-number-list y))))
	  (if (powerlist-p x)
	      (p-merge (p-untie-l x)
		       (p-merge (p-untie-r x) y))
	    (p-insert x y))))

 ;; Our first obligation is that the split functions return smaller powerlists,
 ;; so that we can use split as the basis of recursive definitions.

 (defthm *obligation*-split-reduces-count
   (implies (powerlist-p x)
	    (and (ACL2::e0-ord-< (acl2-count (p-split-1 x))
				 (acl2-count x))
		 (ACL2::e0-ord-< (acl2-count (p-split-2 x))
				 (acl2-count x)))))

 ;; We're annoyed by the next obligation.  We require that when you split/merge
 ;; a list composed of elements over our domain, the result is also composed of
 ;; elements over our domain.  But, this seems subsumed by the following
 ;; requirement, namely that split/merge preserve membership count.  The
 ;; problem is that the following is not an Acl2 theorem:
 ;;
 ;; 	(implies (equal (member-count (foo x) m) (member-count x m))
 ;;		 (implies (numbers x) (numbers (foo x))))
 ;;
 ;; because of the quantification problem on m: we need the forall inside the
 ;; implication.  I have not been able to come up with a satisfying solution to
 ;; this, but if I do, I'll remove the requirement as an assumption and prove
 ;; it outside of the stub.

 (local
  (defthm split-1-of-numbers-is-number-list
    (implies (and (powerlist-p x)
		  (p-number-list x))
	     (p-number-list (p-split-1 x)))
    :rule-classes :type-prescription))

 (local
  (defthm split-2-of-numbers-is-number-list
    (implies (and (powerlist-p x)
		  (p-number-list x))
	     (p-number-list (p-split-2 x)))
    :rule-classes :type-prescription))

 (local
  (defthm merge-of-numbers-is-number-list
    (implies (and (p-number-list x)
		  (p-number-list y))
	     (p-number-list (p-merge x y)))
    :rule-classes :type-prescription))

 (defthm *obligation*-member-count-of-splits
   (implies (powerlist-p x)
	    (equal (+ (p-member-count (p-split-1 x) m)
		      (p-member-count (p-split-2 x) m))
		   (p-member-count x m))))

 (local (defthm member-count-of-insert
	  (implies (numericp e)
		   (equal (p-member-count (p-insert e x) m)
			  (if (= e m)
			      (1+ (p-member-count x m))
			    (p-member-count x m))))))

 (defthm *obligation*-member-count-of-merge
   (implies (p-mergeable-p x y)
	    (equal (p-member-count (p-merge x y) m)
		   (+ (p-member-count x m)
		      (p-member-count y m)))))

 ;; Finally, we require that the result of merging two sorted powerlists is a
 ;; sorted powerlists.  To do that, we start out by proving the result for our
 ;; insert function first.

 (local (defthm max-insert
	  (implies (and (numericp e)
			(p-number-list x))
		   (and (equal (p-max-elem (p-insert e x))
			       (if (> e (p-max-elem x))
				   e
				 (p-max-elem x)))
			(equal (p-min-elem (p-insert e x))
			       (if (< e (p-min-elem x))
				   e
				 (p-min-elem x)))))))

 (local (defthm sorted-insert
	  (implies (and (numericp e)
			(p-number-list x)
			(p-sorted-p x))
		   (p-sorted-p (p-insert e x)))))

 (defthm *obligation*-sorted-merge
   (implies (and (p-mergeable-p x y)
		 (p-sorted-p x)
		 (p-sorted-p y))
	    (p-sorted-p (p-merge x y))))

 (local
  (defthm number-list-merge
    (implies (and (p-number-list x) (p-number-list y))
	     (p-number-list (p-merge x y)))))

 (local
  (defun p-merge-sort (x)
    (declare (xargs :guard (p-number-list x) :verify-guards nil))
    "Sort the powerlist x"
    (if (powerlist-p x)
	(p-merge (p-merge-sort (p-split-1 x))
		 (p-merge-sort (p-split-2 x)))
      x)))

 (local
  (defthm number-list-merge-sort
    (implies (p-number-list x)
	     (p-number-list (p-merge-sort x)))))

 (verify-guards p-merge-sort)

 (defthm *obligation*-merge-sort
   (equal (p-merge-sort x)
	  (if (powerlist-p x)
	      (p-merge (p-merge-sort (p-split-1 x))
		       (p-merge-sort (p-split-2 x)))
	    x))
   :rule-classes (:definition))

 (defthm *obligation*-sortable-split
   (implies (and (powerlist-p x)
		 (p-sortable-p x))
	    (and (p-sortable-p (p-split-1 x))
		 (p-sortable-p (p-split-2 x)))))

 (local
  (defthm merge-sort-of-numbers-is-number-list
    (implies (p-number-list x)
	     (p-number-list (p-merge-sort x)))
    :hints (("Goal"
	     :induct (p-merge-sort x)))
    :rule-classes :type-prescription))

 (defthm *obligation*-sortable-mergeable
   (implies (and (powerlist-p x)
		 (p-sortable-p x))
	    (p-mergeable-p (p-merge-sort
			    (p-split-1 x))
			   (p-merge-sort
			    (p-split-2 x)))))
 )

;; Now that we've stubbed split and merge, we can use them to define our
;; generic merge sort below.


(local
 (defun my-merge-sort (x)
   "Sort the powerlist x"
   (if (powerlist-p x)
       (p-merge (my-merge-sort (p-split-1 x))
		(my-merge-sort (p-split-2 x)))
     x)))

;; The first key property of a correct merge sort is that it permutes its
;; input.  This key requirement keeps sort from being an O(n) algorithm.

(defthm merge-sort-is-permutation
  (implies (p-sortable-p x)
	   (equal (p-member-count (p-merge-sort x) m)
		  (p-member-count x m)))
  :hints (("Goal" :induct (my-merge-sort x))))

;; And finally, we show that with the given assumptions about split/merge, the
;; merge-sort algorithm returns a sorted list.

(defthm merge-sort-sorts-input
  (implies (p-sortable-p x)
	   (p-sorted-p (p-merge-sort x)))
  :hints (("Goal"
	   :induct (my-merge-sort x))))
