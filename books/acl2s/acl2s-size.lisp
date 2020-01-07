(in-package "ACL2")
(include-book "acl2s/cons-size" :dir :system)

(defun acl2s-size (x)
  (declare (xargs :guard t))
  (if (listp x)
      (cons-size x)
    (if (rationalp x)
        (if (integerp x)
            (integer-abs x)
          (+ (integer-abs (numerator x))
             (denominator x)))
      (if (complex/complex-rationalp x)
          (+ 1 (acl2-count (realpart x))
             (acl2-count (imagpart x)))
        (if (stringp x)
            (length x)
          0)))))

(defthm acl2s-size-complex
  (implies (complex/complex-rationalp x)
           (equal (acl2s-size x)
                  (+ 1 (acl2-count (realpart x))
                     (acl2-count (imagpart x)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-string
  (implies (stringp x)
           (equal (acl2s-size x) (length x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-rational
  (implies (and (rationalp x)
                (not (integerp x)))
           (equal (acl2s-size x)
                  (+ (integer-abs (numerator x))
                     (denominator x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-cons
  (implies (listp x)
           (equal (acl2s-size x) (cons-size x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-integer
  (implies (integerp x)
           (equal (acl2s-size x) (integer-abs x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-type
  (natp (acl2s-size x))
  :rule-classes
  ((:type-prescription)
   (:forward-chaining :trigger-terms ((acl2s-size x)))))

(defthm acl2s-size-evens-weak
  (<= (acl2s-size (evens x))
      (acl2s-size x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)

(defthm acl2s-size-of-remove-assoc-equal-upper-bound
  (<= (acl2s-size (remove-assoc-equal a x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable remove-assoc-equal)))
  :rule-classes :linear)

(defthm acl2s-size-of-remove-duplicates
  (<= (acl2s-size (remove-duplicates-equal x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-of-hons-remove-duplicates
  (<= (acl2s-size (acl2::hons-remove-duplicates x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable acl2::hons-remove-duplicates)))
  :rule-classes :linear)

(defthm len-<=-acl2s-size
  (<= (len x) (acl2s-size x))
  :rule-classes :linear)

(defthm acl2-size-append
  (<= (acl2-size (append x y))
      (+ (acl2-size x)
         (acl2-size y)
         1))
  :rule-classes :linear)

(defthm acl2s-size-<=-acl2-count
  (<= (acl2s-size x)
      (acl2-count x))
  :rule-classes :linear)

(in-theory (disable acl2s-size))

