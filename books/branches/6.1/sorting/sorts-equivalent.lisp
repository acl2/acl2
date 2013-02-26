; (certify-book "sorts-equivalent")

(in-package "ACL2")

(include-book "equisort")

(include-book "isort")
(include-book "msort")
(include-book "qsort")
(include-book "bsort")

(defthm msort-is-isort
  (equal (msort x) (isort x))
  :hints (("Goal" :use (:functional-instance strong-ssortfn1-is-ssortfn2
                                             (ssortfn1 (lambda (x) (msort x)))
                                             (ssortfn2 (lambda (x) (isort x)))))))

(defthm qsort-is-isort
  (equal (qsort x) (isort x))
  :hints (("Goal" :use (:functional-instance strong-ssortfn1-is-ssortfn2
                                             (ssortfn1 (lambda (x) (qsort x)))
                                             (ssortfn2 (lambda (x) (isort x)))))))

(defthm bsort-is-isort
  (implies (true-listp x)
           (equal (bsort x) (isort x)))
  :hints (("Goal" :use (:functional-instance weak-sortfn1-is-sortfn2
                                             (sortfn1 (lambda (x) (bsort x)))
                                             (sortfn2 (lambda (x) (isort x)))))))


