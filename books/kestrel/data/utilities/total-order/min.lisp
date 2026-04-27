; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "total-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "total-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-<<-macro-loop
  ((list true-listp))
  :guard (and (consp list)
              (consp (rest list)))
  (if (endp (rest (rest list)))
      (list 'binary-min-<<
            (first list)
            (second list))
    (list 'binary-min-<<
          (first list)
          (min-<<-macro-loop (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(defmacro min-<< (x y &rest rst)
  (declare (xargs :guard t))
  (min-<<-macro-loop (list* x y rst)))

(define binary-min-<< (x y)
  (if (<< x y)
      x
    y)

  ///
  (add-macro-fn min-<< binary-min-<< t))

;;;;;;;;;;;;;;;;;;;;

(defrule min-<<-when-same
  (equal (min-<< x x)
         x)
  :enable min-<<)

(defrule min-<<-when-equal-cheap
  (implies (equal x y)
           (equal (min-<< x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable min-<<)

(defrule min-<<-commutative
  (equal (min-<< y x)
         (min-<< x y))
  :enable (min-<<
           data::<<-rules))

;; Note: this mirrors acl2::commutativity-2-of-+
(defrule min-<<-commutative-2
  (equal (min-<< y x z)
         (min-<< x y z))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (min-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule min-<<-associative
  (equal (min-<< (min-<< x y) z)
         (min-<< x (min-<< y z)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (min-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule min-<<-absorb-left
  (equal (min-<< x x y)
         (min-<< x y))
  :enable min-<<)

(defrule min-<<-absorb-right
  (equal (min-<< y x y)
         (min-<< x y))
  :enable min-<<)

(defrule min-<<-when-<<-of-arg1-and-arg2-cheap
  (implies (<< x y)
           (equal (min-<< x y)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable min-<<)

(defrule min-<<-when-<<-of-arg2-and-arg1-cheap
  (implies (<< y x)
           (equal (min-<< x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable (min-<<
           data::<<-rules))

(defrule <<-of-min-<<
  (equal (<< (min-<< x y) a)
         (or (<< x a)
             (<< y a)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (min-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule <<-of-arg1-and-min-<<
  (equal (<< a (min-<< x y))
         (and (<< a x)
              (<< a y)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x x)
                   (acl2::y a)))
  :enable (min-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule min-<<-when-not-arg1-cheap
  (implies (not (equal (min-<< x y) x))
           (equal (min-<< x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable min-<<)

(defrule min-<<-when-not-arg2-cheap
  (implies (not (equal (min-<< x y) y))
           (equal (min-<< x y)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable min-<<)

(defruled min-<<-monotonic-arg1-inverse
  (implies (<< (min-<< x0 y)
               (min-<< x1 y))
           (<< x0 x1))
  :enable (min-<<
           data::<<-rules))

(defrule min-<<-monotonic-arg1
  (implies (not (<< x0 x1))
           (not (<< (min-<< x0 y)
                    (min-<< x1 y))))
  :by min-<<-monotonic-arg1-inverse)

(defruled min-<<-monotonic-arg2-inverse
  (implies (<< (min-<< x y0)
               (min-<< x y1))
           (<< y0 y1))
  :enable (min-<<
           data::<<-rules))

(defrule min-<<-monotonic-arg2
  (implies (not (<< y0 y1))
           (not (<< (min-<< x y0)
                    (min-<< x y1))))
  :by min-<<-monotonic-arg2-inverse)

(defrule equal-of-min-<<-and-arg1
  (equal (equal (min-<< x y) x)
         (or (equal x y)
             (<< x y)))
  :enable min-<<)

(defrule equal-of-min-<<-and-arg2
  (equal (equal (min-<< x y) y)
         (or (equal x y)
             (<< y x)))
  :enable (min-<<
           data::<<-rules))
