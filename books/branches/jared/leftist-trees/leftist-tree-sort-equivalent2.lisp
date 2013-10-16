; (certify-book "sorts-equivalent2")

(in-package "ACL2")

(include-book "../sorting/equisort2")
(include-book "../sorting/isort")

(include-book "leftist-tree-sort")

(defthm ltree-sort-is-isort
  (implies (true-listp x)
           (equal (ltree-sort x) (isort x)))
  :hints (("Goal" :use (:functional-instance sortfn1-is-sortfn2
                                             (sorthyp true-listp)
                                             (sortfn1 ltree-sort)
                                             (sortfn2 isort)))))
