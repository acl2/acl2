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

(define max-<<-macro-loop
  ((list true-listp))
  :guard (and (consp list)
              (consp (rest list)))
  (if (endp (rest (rest list)))
      (list 'binary-max-<<
            (first list)
            (second list))
    (list 'binary-max-<<
          (first list)
          (max-<<-macro-loop (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(defmacro max-<< (x y &rest rst)
  (declare (xargs :guard t))
  (max-<<-macro-loop (list* x y rst)))

(define binary-max-<< (x y)
  (if (<< x y)
      y
    x)

  ///
  (add-macro-fn max-<< binary-max-<< t))

;;;;;;;;;;;;;;;;;;;;

(defrule max-<<-when-same
  (equal (max-<< x x)
         x)
  :enable max-<<)

(defrule max-<<-when-equal-cheap
  (implies (equal x y)
           (equal (max-<< x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable max-<<)

(defrule max-<<-commutative
  (equal (max-<< y x)
         (max-<< x y))
  :enable (max-<<
           data::<<-rules))

;; Note: this mirrors acl2::commutativity-2-of-+
(defrule max-<<-commutative-2
  (equal (max-<< y x z)
         (max-<< x y z))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (max-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule max-<<-associative
  (equal (max-<< (max-<< x y) z)
         (max-<< x (max-<< y z)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (max-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule max-<<-absorb-left
  (equal (max-<< x x y)
         (max-<< x y))
  :enable max-<<)

(defrule max-<<-absorb-right
  (equal (max-<< y x y)
         (max-<< x y))
  :enable max-<<)

(defrule max-<<-when-<<-of-arg1-and-arg2-cheap
  (implies (<< x y)
           (equal (max-<< x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable max-<<)

(defrule max-<<-when-<<-of-arg2-and-arg1-cheap
  (implies (<< y x)
           (equal (max-<< x y)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable (max-<<
           data::<<-rules))

(defrule <<-of-max-<<
  (equal (<< (max-<< x y) a)
         (and (<< x a)
              (<< y a)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (max-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule <<-of-arg1-and-max-<<
  (equal (<< a (max-<< x y))
         (or (<< a x)
             (<< a y)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (max-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule max-<<-when-not-arg1-cheap
  (implies (not (equal (max-<< x y) x))
           (equal (max-<< x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable max-<<)

(defrule max-<<-when-not-arg2-cheap
  (implies (not (equal (max-<< x y) y))
           (equal (max-<< x y)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable max-<<)

(defruled max-<<-monotonic-arg1-inverse
  (implies (<< (max-<< x0 y)
               (max-<< x1 y))
           (<< x0 x1))
  :enable (max-<<
           data::<<-rules))

(defrule max-<<-monotonic-arg1
  (implies (not (<< x0 x1))
           (not (<< (max-<< x0 y)
                    (max-<< x1 y))))
  :by max-<<-monotonic-arg1-inverse)

(defruled max-<<-monotonic-arg2-inverse
  (implies (<< (max-<< x y0)
               (max-<< x y1))
           (<< y0 y1))
  :enable (max-<<
           data::<<-rules))

(defrule max-<<-monotonic-arg2
  (implies (not (<< y0 y1))
           (not (<< (max-<< x y0)
                    (max-<< x y1))))
  :by max-<<-monotonic-arg2-inverse)

(defrule equal-of-max-<<-and-arg1
  (equal (equal (max-<< x y) x)
         (or (equal x y)
             (<< y x)))
  :enable (max-<<
           data::<<-rules))

(defrule equal-of-max-<<-and-arg2
  (equal (equal (max-<< x y) y)
         (or (equal x y)
             (<< x y)))
  :enable max-<<)
