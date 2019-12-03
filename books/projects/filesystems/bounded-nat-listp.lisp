(in-package "ACL2")

(defun bounded-nat-listp (l b)
  (declare (xargs :guard (natp b)))
  (if (atom l)
      (equal l nil)
      (and (natp (car l))
           (< (car l) b)
           (bounded-nat-listp (cdr l) b))))

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
  (implies (and (bounded-nat-listp l (+ b 1))
                (natp b)
                (not (bounded-nat-listp l b)))
           (member-equal b l))
  :rule-classes :forward-chaining)

(defthm bounded-nat-listp-correctness-4
  (implies (bounded-nat-listp l b)
           (not (member-equal b l)))
  :rule-classes :forward-chaining)

(defthmd bounded-nat-listp-correctness-5
  (implies (and (<= x y) (bounded-nat-listp l x))
           (bounded-nat-listp l y)))

(defthm bounded-nat-listp-of-make-list-ac
  (implies (and (bounded-nat-listp ac b) (natp val) (< val b))
           (bounded-nat-listp (make-list-ac n val ac) b)))

(defthm car-of-last-when-bounded-nat-listp
  (implies (and (< 0 b) (bounded-nat-listp l b))
           (< (car (last l)) b))
  :hints (("goal" :induct (bounded-nat-listp l b)))
  :rule-classes :linear)

(defun lower-bounded-integer-listp (l b)
  (declare (xargs :guard (integerp b)))
  (if (atom l)
      (equal l nil)
      (and (integerp (car l))
           (>= (car l) b)
           (lower-bounded-integer-listp (cdr l)
                                        b))))

(defthm lower-bounded-integer-listp-correctness-2
  (implies (true-listp x)
           (equal (lower-bounded-integer-listp (binary-append x y)
                                     b)
                  (and (lower-bounded-integer-listp x b)
                       (lower-bounded-integer-listp y b)))))

(defthmd lower-bounded-integer-listp-correctness-5
  (implies (and (<= y x) (lower-bounded-integer-listp l x))
           (lower-bounded-integer-listp l y)))

(defthm lower-bounded-integer-listp-of-remove
  (implies (lower-bounded-integer-listp l b)
           (lower-bounded-integer-listp (remove-equal x l) b)))
