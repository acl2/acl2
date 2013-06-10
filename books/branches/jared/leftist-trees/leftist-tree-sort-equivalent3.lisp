; (certify-book "sorts-equivalent3")

(in-package "ACL2")

(include-book "../sorting/equisort3")
(include-book "../sorting/isort")

(include-book "leftist-tree-sort")

(defthm ltree-sort-is-isort
  (implies (true-listp x)
           (equal (ltree-sort x) (isort x)))
  :hints (("Goal" :in-theory (e/d (equisort) (ltree-sort isort)))))

