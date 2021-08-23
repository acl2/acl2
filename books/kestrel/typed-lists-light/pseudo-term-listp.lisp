; A lightweight book about the built-in function pseudo-term-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This books treats pseudo-term-listp like any other list processor.  But see
;; also pseudo-termp.lisp.

(defthm pseudo-termp-of-nth
  (implies (pseudo-term-listp l)
           (pseudo-termp (nth n l)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp nth))))

(defthm pseudo-termp-of-car-when-pseudo-term-listp-cheap
  (implies (pseudo-term-listp terms)
           (pseudo-termp (car terms)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-of-cdr-when-pseudo-term-listp-cheap
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (cdr terms)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

;; name clash with std
(defthm pseudo-term-listp-of-union-equal-2
  (equal (pseudo-term-listp (union-equal x y))
         (and (pseudo-term-listp (true-list-fix x))
              (pseudo-term-listp y)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp union-equal))))

(defthm pseudo-term-listp-of-intersection-equal
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp intersection-equal))))

;; The non-standard variable names are to match STD
(defthm pseudo-term-listp-of-remove-equal
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (remove-equal a x)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp remove-equal))))

;; Removing a pseudo-term shouldn't affect whether a list contains only pseudo-terms
(defthm pseudo-term-listp-of-remove-equal-alt
  (implies (and (pseudo-termp x)
                (true-listp l))
           (equal (pseudo-term-listp (remove-equal x l))
                  (pseudo-term-listp l)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp remove-equal))))

;; Matches the version in STD
(defthm pseudo-term-listp-of-cons
  (equal (pseudo-term-listp (cons a x))
         (and (pseudo-termp a)
              (pseudo-term-listp x)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-of-revappend
  (equal (pseudo-term-listp (revappend x y))
         (and (pseudo-term-listp (true-list-fix x))
              (pseudo-term-listp y)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-of-true-list-fix
  (implies (pseudo-term-listp lst)
           (pseudo-term-listp (true-list-fix lst)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

;; Kept disabled
;; Avoids name clash with STD, where the rule is a :compound-recognizer
(defthmd true-listp-when-pseudo-term-listp-2
  (implies (pseudo-term-listp lst)
           (true-listp lst))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))
