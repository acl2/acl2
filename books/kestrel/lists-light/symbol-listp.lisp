; A lightweight book about the built-in function symbol-listp.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also books/std/typed-lists/symbol-listp.lisp, but that book may be more
;; heavyweight.

;; Avoid name clash with std.
(defthm symbol-listp-of-set-difference-equal-alt
  (implies (symbol-listp l1)
           (symbol-listp (set-difference-equal l1 l2))))

(defthm symbol-listp-of-append2
  (equal (symbol-listp (append x y))
         (and (symbol-listp (true-list-fix x))
              (symbol-listp y)))
  :hints (("Goal" :in-theory (enable append symbol-listp))))

;this had a name conflict with a theorem in std/typed-lists/symbol-listp
(defthm symbol-listp-of-union-equal-alt
  (equal (symbol-listp (union-equal l1 l2))
         (and (symbol-listp (true-list-fix l1))
              (symbol-listp l2))))

(defthm symbol-listp-of-intersection-equal
  (implies (or (symbol-listp l1)
               (symbol-listp l2))
           (symbol-listp (intersection-equal l1 l2))))

(defthm symbol-listp-of-add-to-set-equal
  (equal (symbol-listp (add-to-set-equal x l))
         (and (symbolp x)
              (symbol-listp l)))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm symbol-listp-of-cdr
  (implies (symbol-listp x)
           (symbol-listp (cdr x)))
  :hints (("Goal" :in-theory (enable symbol-listp))))

(defthm symbol-listp-of-cons
  (equal (symbol-listp (cons a x))
         (and (symbolp a)
              (symbol-listp x)))
  :hints (("Goal" :in-theory (enable symbol-listp))))

(defthm symbol-listp-of-true-list-fix
  (implies (symbol-listp x)
           (symbol-listp (true-list-fix x))))

;; Disabled but see symbolp-of-car-when-symbol-listp.
(defthmd symbolp-of-car-when-symbol-listp
  (implies (symbol-listp x)
           (symbolp (car x)))
  :hints (("Goal" :in-theory (enable symbol-listp))))

(defthm symbolp-of-car-when-symbol-listp-cheap
  (implies (symbol-listp x)
           (symbolp (car x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-listp))))
