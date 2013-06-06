; (certify-book "sorts-equivalent")

(in-package "ACL2")

(include-book "../sorting/equisort")
(include-book "../sorting/isort")

(include-book "leftist-tree-sort")

(defthm ltree-sort-is-isort
  (implies (true-listp x)
           (equal (ltree-sort x) (isort x)))
  :hints (("Goal" :use (:functional-instance weak-sortfn1-is-sortfn2
                                             (sortfn1 (lambda (x) (ltree-sort x)))
                                             (sortfn2 (lambda (x) (isort x)))))))
