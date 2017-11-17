(in-package "ACL2")

(defun bounded-nat-listp (l b)
  (declare (xargs :guard (natp b)))
  (if (atom l)
      (equal l nil)
    (and (natp (car l)) (< (car l) b) (bounded-nat-listp (cdr l) b))))

(defthm bounded-nat-listp-correctness-1
  (implies (bounded-nat-listp l b)
           (nat-listp l))
  :rule-classes (:rewrite :forward-chaining))

(defthm bounded-nat-listp-correctness-2
  (implies (true-listp x)
           (equal (bounded-nat-listp (binary-append x y)
                                     b)
                  (and (bounded-nat-listp x b)
                       (bounded-nat-listp y b)))))

(defthm bounded-nat-listp-correctness-3
  (implies (and (natp b)
                (bounded-nat-listp l (+ b 1))
                (not (bounded-nat-listp l b)))
           (member-equal b l)))

(defthm bounded-nat-listp-correctness-4
  (implies (bounded-nat-listp l b)
           (not (member-equal b l))))
