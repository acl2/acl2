(in-package "ACL2")

(include-book "all-equal-dollar")

;todo: disable
(defun all-same (lst)
  (declare (xargs :guard (true-listp lst)))
  (or (atom lst)
      (all-equal$ (car lst) (cdr lst))))

(defthm booleanp-of-all-same
  (booleanp (all-same lst)))

(defthmd nth-when-all-same
  (implies (and (all-same lst)
                (integerp x))
           (equal (nth x lst)
                  (if (< x (len lst))
                      (first lst)
                    nil)))
  :hints (("Goal" :in-theory (e/d ((:i nth) all-equal$) (;nth-of-cdr
                                                    )))))

(defthm nth-when-all-same-cheap
  (implies (and (syntaxp (quotep lst))
                (all-same lst)
                (integerp x))
           (equal (nth x lst)
                  (if (< x (len lst))
                      (first lst)
                    nil)))
  :hints (("Goal" :use (:instance nth-when-all-same)
           :in-theory (disable nth-when-all-same))))
