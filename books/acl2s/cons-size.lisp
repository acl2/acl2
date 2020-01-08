(in-package "ACL2")
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "defexec/other-apps/records/records" :dir :system)

(defun cons-size (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1 (cons-size (car x)) (cons-size (cdr x)))
    0))

(defmacro tree-size (x)
  `(cons-size ,x))
  
(defthm cons-size-type
  (natp (cons-size x))
  :rule-classes
  ((:type-prescription)
   (:forward-chaining :trigger-terms ((cons-size x)))))

(defthm acons-cons-size-lemma
  (= (cons-size (acons x1 x2 x3))
     (+ 2 (cons-size x1)
        (cons-size x2)
        (cons-size x3)))
  :rule-classes ((:linear) (:rewrite)))

(defthm split-list-1-cons-size
  (implies (consp x)
           (< (cons-size (mv-nth 1 (str::split-list-1 x str::del)))
              (cons-size x)))
  :hints (("Goal" :in-theory (enable str::split-list-1)))
  :rule-classes :linear)

(defthm head-cons-size
  (implies (not (set::empty x))
           (< (cons-size (set::head x))
              (cons-size x)))
  :hints (("Goal" :in-theory (enable set::empty set::head)))
  :rule-classes :linear)

(defthm tail-cons-size
  (implies (not (set::empty x))
           (< (cons-size (set::tail x))
              (cons-size x)))
  :hints (("Goal" :in-theory (enable set::empty set::tail)))
  :rule-classes :linear)

(defthm cons-size-append
  (= (cons-size (append x y))
     (+ (cons-size x) (cons-size y)))
  :rule-classes ((:linear) (:rewrite)))

(defthm rev-cons-size-lemma
  (= (cons-size (rev x))
     (cons-size x))
  :hints (("Goal" :in-theory (enable rev)))
  :rule-classes ((:linear) (:rewrite)))

(defthm cons-size-evens-strong
  (implies (and (consp x)
                (consp (cdr x)))
           (< (cons-size (evens x))
              (cons-size x)))
  :rule-classes :linear)

(defthm cons-size-evens-weak
  (<= (cons-size (evens x))
      (cons-size x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)

(defthm cons-size-of-remove-assoc-equal-upper-bound
  (<= (cons-size (remove-assoc-equal a x))
      (cons-size x))
  :hints (("Goal" :in-theory (enable remove-assoc-equal)))
  :rule-classes :linear)

(defthm cons-size-when-member
  (implies (member-equal a x)
           (< (cons-size a)
              (cons-size x)))
  :hints (("Goal" :in-theory (enable member-equal)))
  :rule-classes :linear)

(defthm cons-size-of-remove-duplicates
  (<= (cons-size (remove-duplicates-equal x))
      (cons-size x))
  :rule-classes :linear)

(defthm cons-size-of-hons-remove-duplicates
  (<= (cons-size (acl2::hons-remove-duplicates x))
      (cons-size x))
  :hints (("Goal" :in-theory (enable acl2::hons-remove-duplicates)))
  :rule-classes :linear)

(defthm cons-size-of-nthcdr-linear
  (implies (and (not (zp n)) (consp x))
           (< (cons-size (nthcdr n x))
              (cons-size x)))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes :linear)

(defthm cons-size-of-nthcdr-linear-weak
  (<= (cons-size (nthcdr n x))
      (cons-size x))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes :linear)

(defthm cons-size-of-nth-linear-weak
  (<= (cons-size (nth i x))
      (cons-size x))
  :rule-classes :linear)

(defthm cons-size-of-nth-linear
  (implies  (consp x)
            (< (cons-size (nth i x))
               (cons-size x)))
  :rule-classes :linear)

(defthm cons-size-of-prod-cons1
  (<= (cons-size std::y)
      (cons-size (std::prod-cons std::x std::y)))
  :rule-classes :linear)

(defthm cons-size-of-prod-cons2
  (<= (cons-size std::x)
      (cons-size (std::prod-cons std::x std::y)))
  :rule-classes :linear)

(defthm records-lemma-cons-size
  (implies (and (acl2::ifmp v)
                (acl2::well-formed-map v))
           (< (cons-size (acl2::mget-wf x v))
              (cons-size v)))
  :hints (("goal" :in-theory (enable acl2::mget-wf)))
  :rule-classes :linear)

(defthm records-cons-size-linear-arith-<=
  (<= (cons-size (mget k v))
      (cons-size v))
  :hints (("goal" :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm records-cons-size-linear-arith-<
  (implies (and (not (equal k (acl2::ill-formed-key)))
                (mget k v))
           (< (cons-size (mget k v))
              (cons-size v)))
  :hints (("goal" :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm records-cons-size
  (implies (and (consp v)
                (not (equal x (acl2::ill-formed-key))))
           (< (cons-size (mget x v))
              (cons-size v)))
  :hints (("goal" :induct (acl2::mget-wf x v)
           :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm len-<=-cons-size
  (<= (len x) (cons-size x))
  :rule-classes :linear)

(defthm cons-size-<=-acl2-count
  (<= (cons-size x)
      (acl2-count x))
  :rule-classes :linear)

; This shows that cons-size can be used to prove termination of
; acl2-count (which is what acl2-size is).

(defun acl2-size (x)
  (declare (xargs :guard t
                  :measure (if (and (not (rationalp x))
                                    (complex/complex-rationalp x))
                               1
                             (* 2 (cons-size x)))))
  (if (consp x)
      (+ 1 (acl2-size (car x))
         (acl2-size (cdr x)))
    (if (rationalp x)
        (if (integerp x)
            (integer-abs x)
          (+ (integer-abs (numerator x))
             (denominator x)))
      (if (complex/complex-rationalp x)
          (+ 1 (acl2-size (realpart x))
             (acl2-size (imagpart x)))
        (if (stringp x)
            (length x)
          0)))))
