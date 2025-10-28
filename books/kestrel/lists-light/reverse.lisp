; A lightweight book about the built-in function reverse.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that it may be helpful, instead of reasoning about reverse, to get
;; rid of it in favor of rev or reverse-list.

(local (include-book "revappend"))
(local (include-book "true-list-fix"))

(in-theory (disable reverse))

(defthm len-of-reverse
  (equal (len (reverse x))
         (len x))
  :hints (("Goal" :in-theory (enable reverse))))

;; copied from std/lists/reverse.lisp
(defthm true-listp-of-reverse
  (equal (true-listp (reverse x))
         (not (stringp x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm reverse-of-cons
  (equal (reverse (cons a x))
         (append (reverse x)
                 (list a)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm consp-of-reverse
  (equal (consp (reverse x))
         (consp x))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm car-of-reverse
  (equal (car (reverse x))
         (car (last x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm <=-of-acl2-count-of-reverse-linear
  (<= (acl2-count (reverse x))
      (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable reverse))))

(defthm stringp-of-reverse
  (equal (stringp (reverse x))
         (stringp x))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm stringp-of-reverse-type
  (implies (stringp x)
           (stringp (reverse x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable reverse))))

(defthm member-equal-of-reverse-iff
  (iff (member-equal a (reverse x))
       (member-equal a x))
  :hints (("Goal" :in-theory (enable reverse))))

;; injectivity (almost)
(defthm equal-of-reverse-and-reverse-when-true-lists
  (implies (and (true-listp x) ; excludes the string case
                (true-listp y))
           (equal (equal (reverse x) (reverse y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable reverse))))
