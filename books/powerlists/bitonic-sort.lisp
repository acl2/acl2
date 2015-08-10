#|

This is in an ACL2 "book" defining a bitonic-merge sort for powerlists.  It
also presents a specific bitonic sort using this bitonic merge.  We show that
the given bitonic sort is equal to the batcher merge sort, and hence it
correctly sorts its input.  This book, as well as others working with
powerlists, is described in the paper "Defthms About Zip and Tie", UTCS tech
report TR97-02.

To compile the book, I do the following:

    (ld ;; Newline to fool dependency scanner
      "defpkg.lisp")
    (certify-book "bitonic-sort" 4)
    (in-package "POWERLISTS")

|#

(in-package "POWERLISTS")
(include-book "algebra")
(include-book "simple")
(include-book "sort")
(include-book "batcher-sort")
(include-book "arithmetic/top" :dir :system :load-compiled-file nil)

(set-verify-guards-eagerness 2)

;;; We begin by defining a simple bitonic merge and a sample bitonic sort that
;;; uses the bitonic merge

(defun p-bitonic-merge (x)
  "Given a bitonic list, returns a sorted list"
  (declare (xargs :guard (and (p-regular-p x)
			      (p-number-list x))
		  :verify-guards nil))
  (if (powerlist-p x)
      (p-zip (p-min (p-bitonic-merge (p-unzip-l x))
		    (p-bitonic-merge (p-unzip-r x)))
	     (p-max (p-bitonic-merge (p-unzip-l x))
		    (p-bitonic-merge (p-unzip-r x))))
    x))

(defun p-bitonic-sort (x)
  "Given a list, returns a sorted list"
  (declare (xargs :guard (and (p-regular-p x)
			      (p-number-list x))
		  :verify-guards nil))
  (if (powerlist-p x)
      (p-bitonic-merge (p-tie (p-bitonic-sort (p-untie-l x))
			      (p-reverse (p-bitonic-sort (p-untie-r x)))))
    x))

;;; Unfortunately, we must begin by proving properties about the shape of the
;;; lists we're dealing with.  This is the big disadvantage of not using
;;; strictly regular powerlists as Misra suggests.

(defthm powerlist-reverse
  (equal (powerlist-p (p-reverse x))
	 (powerlist-p x)))

(defthm unzip-reverse
  (implies (powerlist-p x)
	   (and (equal (p-unzip-l (p-reverse x))
		       (p-reverse (p-unzip-r x)))
		(equal (p-unzip-r (p-reverse x))
		       (p-reverse (p-unzip-l x))))))

(defthm similar-bitonic-merge
  (implies (p-regular-p x)
	   (p-similar-p (p-bitonic-merge x) x)))

(defthm similar-reverse
  (implies (p-regular-p x)
	   (p-similar-p (p-reverse x) x)))

(defthm powerlist-p-zip
  (equal (powerlist-p (p-zip x y)) t))

(defthm powerlist-bitonic-merge
  (equal (powerlist-p (p-bitonic-merge x))
	 (powerlist-p x)))

(defthm powerlist-bitonic-sort
  (equal (powerlist-p (p-bitonic-sort x))
	 (powerlist-p x)))

(defthm similar-bitonic-sort-aux
  (implies (and (p-regular-p x)
		(p-regular-p y)
		(p-similar-p (p-bitonic-sort x) x)
		(p-similar-p (p-bitonic-sort y) y)
		(p-similar-p x y))
	   (p-regular-p (p-tie (p-bitonic-sort x)
			       (p-reverse (p-bitonic-sort y))))))

(defthm similar-bitonic-sort
  (implies (p-regular-p x)
	   (p-similar-p (p-bitonic-sort x) x)))

(defthm regular-bitonic-sort
  (implies (p-regular-p x)
	   (p-regular-p (p-bitonic-sort x)))
  :hints (("Goal" :use (:instance similar-bitonic-sort)
	   :in-theory (disable similar-bitonic-sort))))

;;; Now, we can prove the fundamental result, namely that the bitonic sort
;;; returns the same value as the batcher-sort

(encapsulate
 ()

 (local
  (defthm bitonic-batcher-merge
    (implies (and (p-regular-p x)
		  (p-similar-p x y))
	     (equal (p-bitonic-merge (p-tie x (p-reverse y)))
		    (p-batcher-merge x y)))))

 (defthm bitonic-batcher-sort
   (implies (p-regular-p x)
	    (equal (p-bitonic-sort x)
		   (p-batcher-sort x)))
   :hints (("Subgoal *1/2"
	    :expand (p-bitonic-sort x)
	    :in-theory (disable p-bitonic-sort))
	   ("Subgoal *1/2'"
	    :use (:instance bitonic-batcher-merge
			    (x (p-batcher-sort (p-untie-l x)))
			    (y (p-batcher-sort (p-untie-r x))))
	    :in-theory (disable bitonic-batcher-merge)))))



;;; The remaining theorems, which detail the correctness of this specific
;;; bitonic sort algorithm, are simple consequences of the theorem above.

(defthm bitonic-sort-is-permutation
  (implies (and (p-regular-p x)
		(p-number-list x))
	   (equal (p-member-count (p-bitonic-sort x) m)
		  (p-member-count x m))))

(defthm bitonic-sort-sorts-inputs
  (implies (and (p-regular-p x)
		(p-number-list x))
	   (p-sorted-p (p-bitonic-sort x))))

(defthm number-list-bitonic-merge
  (implies (powerlist-p x)
	   (p-number-list (p-bitonic-merge x))))

(defthm number-list-bitonic-sort
  (implies (powerlist-p x)
	   (p-number-list (p-bitonic-sort x))))

(defthm regular-reverse
  (implies (p-regular-p x)
	   (p-regular-p (p-reverse x))))

(defthm number-list-reverse
  (equal (p-number-list (p-reverse x))
	 (p-number-list x)))

(verify-guards p-bitonic-merge)
(verify-guards p-bitonic-sort)
