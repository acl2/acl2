(in-package "ACL2")
(include-book "acl2s/cons-size" :dir :system)

(defun acl2s-size (x)
  (declare (xargs :guard t))
  (cond ((consp x)
         (+ 1 (acl2s-size (car x))
            (acl2s-size (cdr x))))
        ((rationalp x)
         (integer-abs (numerator x)))
        ((stringp x)
         (length x))
        (t 0)))

(defthm acl2s-size-string
  (implies (stringp x)
           (equal (acl2s-size x) (length x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-rational
  (implies (rationalp x)
           (equal (acl2s-size x)
                  (integer-abs (numerator x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

#|

 Causes rewrite loops. Seems like an ACL2 bug, or at least there is a
 potential for improvement since we should catch such rewrite
 loops. Investigate at some point.

(defthm acl2s-size-cons
  (implies (consp (double-rewrite x))
           (equal (acl2s-size x)
                  (+ 1 (acl2s-size (car (double-rewrite x)))
                     (acl2s-size (cdr (double-rewrite x))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

|#

(defthm acl2s-size-else
  (implies (and (atom (double-rewrite x))
                (not (rationalp x))
                (not (stringp x)))
           (equal (acl2s-size x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-type
  (natp (acl2s-size x))
  :rule-classes
  ((:type-prescription)
   (:forward-chaining :trigger-terms ((acl2s-size x)))))

(defthm acons-acl2s-size-lemma
  (= (acl2s-size (acons x1 x2 x3))
     (+ 2 (acl2s-size x1)
        (acl2s-size x2)
        (acl2s-size x3)))
  :rule-classes ((:linear) (:rewrite)))

(defthm acl2s-size-of-prod-cons1
  (<= (acl2s-size std::y)
      (acl2s-size (std::prod-cons std::x std::y)))
  :rule-classes :linear)

(defthm acl2s-size-of-prod-cons2
  (<= (acl2s-size std::x)
      (acl2s-size (std::prod-cons std::x std::y)))
  :rule-classes :linear)

(defthm acl2s-size-of-nth-linear
  (implies (consp (double-rewrite x))
           (< (acl2s-size (nth i x))
              (acl2s-size x)))
  :rule-classes :linear)

(defthm acl2s-size-of-nth-linear-weak
  (<= (acl2s-size (nth i x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-of-nthcdr-linear
  (implies (and (not (zp (double-rewrite n)))
                (consp (double-rewrite x)))
           (< (acl2s-size (nthcdr n x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes :linear)

(defthm acl2s-size-of-nthcdr-linear-weak
  (<= (acl2s-size (nthcdr n x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes :linear)

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm acl2s-size-of-remove-duplicates
   (<= (acl2s-size (remove-duplicates-equal x))
       (acl2s-size x))
   :rule-classes :linear))

(defthm acl2s-size-when-member
  (implies (member-equal a (double-rewrite x))
           (< (acl2s-size a)
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable member-equal)))
  :rule-classes ((:linear :match-free :all)
                 (:rewrite :backchain-limit-lst 1 :match-free :all)))

(defthm acl2s-size-of-remove-assoc-equal-upper-bound
  (<= (acl2s-size (remove-assoc-equal a x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable remove-assoc-equal)))
  :rule-classes :linear)

(defthm tail-acl2s-size
  (implies (not (set::empty x))
           (< (acl2s-size (set::tail x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable set::empty set::tail)))
  :rule-classes ((:rewrite :backchain-limit-lst 0) (:linear)))

(defthm head-acl2s-size
  (implies (not (set::empty x))
           (< (acl2s-size (set::head x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable set::empty set::head)))
  :rule-classes ((:rewrite :backchain-limit-lst 0) (:linear)))

(defthm split-list-1-acl2s-size
  (implies (consp (double-rewrite x))
           (< (acl2s-size (mv-nth 1 (str::split-list-1 x str::del)))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable str::split-list-1)))
  :rule-classes ((:rewrite :backchain-limit-lst 0) (:linear)))

(defthm records-lemma-acl2s-size
  (implies (and (acl2::ifmp v)
                (acl2::well-formed-map v))
           (< (acl2s-size (acl2::mget-wf x v))
              (acl2s-size v)))
  :hints (("goal" :in-theory (enable acl2::mget-wf)))
  :rule-classes :linear)
 
(defthm records-acl2s-size-linear-arith-<=
  (<= (acl2s-size (mget k v))
      (acl2s-size v))
  :hints (("goal" :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm records-acl2s-size-linear-arith-<2
  (implies (and (not (equal k (acl2::ill-formed-key)))
                (mget k v))
           (< (acl2s-size (mget k v))
              (acl2s-size v)))
  :hints (("goal" :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm records-acl2s-size
  (implies (and (consp v)
                (not (equal x (acl2::ill-formed-key))))
           (< (acl2s-size (mget x v))
              (acl2s-size v)))
  :hints (("goal" :induct (acl2::mget-wf x v)
           :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm acl2s-size-evens-strong
  (implies (consp (cdr (double-rewrite x)))
           (< (acl2s-size (evens x))
              (acl2s-size x)))
  :rule-classes :linear)

(defthm acl2s-size-evens-weak
  (<= (acl2s-size (evens x))
      (acl2s-size x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)

(defthm acl2s-size-append-tlp
  (implies (and (true-listp x) (true-listp y))
           (= (acl2s-size (append x y))
              (+ (acl2s-size x) (acl2s-size y))))
  :hints (("goal" :in-theory (enable append)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))
           
(defthm acl2-size-append
  (<= (acl2-size (append x y))
      (+ (acl2-size x) (acl2-size y) 1))
  :rule-classes ((:linear) (:rewrite)))

#|

 Maybe a replacement for car-of-append

(defthm car-of-append-backchain
  (implies (consp (double-rewrite x))
           (equal (car (append x y))
                  (car x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
|#

(defthm rev-acl2s-size-tlp
  (implies (true-listp x)
           (= (acl2s-size (rev x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable rev)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm rev-acl2s-size
  (<= (acl2s-size (rev x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (e/d (rev))))
  :rule-classes :linear)

(defthm acl2s-size-of-hons-remove-duplicates
  (<= (acl2s-size (acl2::hons-remove-duplicates x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable acl2::hons-remove-duplicates)))
  :rule-classes ((:linear) (:rewrite)))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm acl2s-size-<=-acl2-count
   (<= (acl2s-size x)
       (acl2-count x))
   :rule-classes :linear))

#|

 There seems to be no way to get rid of the double-rewrite warning
 without introducing a non-rec warning. Is this what is supposed to
 happen?

|#

(defthm len-<=-acl2s-size
  (<= (len x) (acl2s-size x))
  :rule-classes :linear)

