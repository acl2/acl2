(in-package "ACL2")

#|

  split-qs-properties.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~~

In this book we make clear the relation between split-qs and the functions walk
and merge-func we described earlier. These properties will allow us to reason
when we prove that sort-qs is equal to in-situ-qsort-fn using sort-qs as the
induction hint.

|#

(include-book "programs")
(include-book "merge-intermediate")
(include-book "extraction")
(include-book "arithmetic/top-with-meta" :dir :system)

(local
(in-theory (enable swap))
)

(local
(defthm arith-001
  (implies (and (not (natp (1- hi)))
                (natp hi))
           (equal hi 0))
  :rule-classes :forward-chaining)
)


(defthm walk-split-qs-equal
  (implies (and (natp lo)
                (natp hi))
	   (equal (mv-nth 0 (split-qs lo hi splitter qs))
		  (+ lo (walk (extract-qs lo hi qs) splitter))))
  :hints (("Goal"
	   :induct (split-qs lo hi splitter qs))))



(defthm split-qs-is-identity-for-below-range
  (implies (and (natp i)
                (natp lo)
                (natp hi)
                (< i lo))
           (equal (objsi i (mv-nth 1 (split-qs lo hi splitter qstor)))
                  (objsi i qstor))))

(defthm split-qs-is-identity-for-above-range
  (implies (and (natp i)
                (natp lo)
                (natp hi)
                (> i hi))
           (equal (objsi i (mv-nth 1 (split-qs lo hi splitter qstor)))
                  (objsi i qstor))))

(defthm merge-func-split-qs-equal
  (implies (and (natp lo)
                (natp hi))
           (equal (extract-qs lo hi (mv-nth 1 (split-qs lo hi splitter qs)))
                  (merge-func (extract-qs lo hi qs) splitter)))
  :hints (("Goal"
	   :induct (split-qs lo hi splitter qs))))


(in-theory (disable extract-qs-decrement-hi))



(in-theory (disable walk-split-qs-equal))

