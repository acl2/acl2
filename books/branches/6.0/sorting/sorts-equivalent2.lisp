; (certify-book "sorts-equivalent2")

(in-package "ACL2")

(include-book "equisort2")

(include-book "isort")
(include-book "msort")
(include-book "qsort")
(include-book "bsort")

(defthm msort-is-isort
  (equal (msort x) (isort x))
  :hints (("Goal" :use (:functional-instance sortfn1-is-sortfn2
                                             (sorthyp (lambda (x) t))
                                             (sortfn1 msort)
                                             (sortfn2 isort)))))

(defthm qsort-is-isort
  (equal (qsort x) (isort x))
  :hints (("Goal" :use (:functional-instance sortfn1-is-sortfn2
                                             (sorthyp (lambda (x) t))
                                             (sortfn1 qsort)
                                             (sortfn2 isort)))))

(defthm bsort-is-isort
  (implies (true-listp x)
           (equal (bsort x) (isort x)))
  :hints (("Goal" :use (:functional-instance sortfn1-is-sortfn2
                                             (sorthyp true-listp)
                                             (sortfn1 bsort)
                                             (sortfn2 isort)))))


