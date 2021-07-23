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

;; Avoids name clash with std
(defthm symbol-listp-of-take-simple
  (implies (symbol-listp l)
           (symbol-listp (take n l)))
  :hints (("Goal" :in-theory (enable take))))

;; Avoids name clash with std
(defthm symbol-listp-of-nthcdr-simple
  (implies (symbol-listp l)
           (symbol-listp (nthcdr n l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm symbol-listp-of-revappend
  (equal (symbol-listp (revappend x y))
         (and (symbol-listp (true-list-fix x))
              (symbol-listp y)))
  :hints (("Goal" :in-theory (enable revappend symbol-listp))))

(defthm symbol-listp-of-reverse
  (implies (symbol-listp x)
           (symbol-listp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

;this matches something in STD
(defthm true-listp-when-symbol-listp
  (implies (symbol-listp x)
           (true-listp x))
  :rule-classes :compound-recognizer)

;; Can't call this true-listp-when-symbol-listp because std uses that name for a :compound-recognizer rule.
;; Can't call this true-listp-when-symbol-listp-rewrite because std uses that name for a backchain-limited rule.
(defthmd true-listp-when-symbol-listp-rewrite-unlimited
  (implies (symbol-listp x)
           (true-listp x)))

; may be nil, which is a symbol!
(defthm symbolp-of-car-of-last-when-symbol-listp
  (implies (symbol-listp x)
           (symbolp (car (last x))))
  :hints (("Goal" :in-theory (enable symbol-listp))))
