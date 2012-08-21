; (certify-book "sorts-equivalent3")

(in-package "ACL2")

(include-book "equisort3")

(include-book "isort")
(include-book "msort")
(include-book "qsort")
(include-book "bsort")

(defthm msort-is-isort
  (equal (msort x) (isort x))
  :hints (("Goal" :in-theory (enable equisort))))

(defthm qsort-is-isort
  (equal (qsort x) (isort x))
  :hints (("Goal" :in-theory (enable equisort))))

(defthm bsort-is-isort
  (implies (true-listp x)
           (equal (bsort x) (isort x)))
  :hints (("Goal" :in-theory (e/d (equisort) (bsort isort)))))



