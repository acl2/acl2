; A lightweight book about the built-in function last.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable last))

;; Use the param name x to match books/kestrel/utilities/lists/last-theorems.lisp.
(defthm last-of-cdr
  (equal (last (cdr x))
         (if (consp (cdr x))
             (last x)
           (cdr x)))
  :hints (("Goal" :in-theory (enable last))))

(defthmd car-of-last-becomes-nth
  (equal (car (last lst))
         (nth (+ -1 (len lst)) lst))
  :hints (("Goal" :in-theory (enable last))))

(defthmd nth-of-len-minus-1-becomes-car-of-last
  (equal (nth (+ -1 (len lst)) lst)
         (car (last lst)))
  :hints (("Goal" :in-theory (enable last))))

(theory-invariant (incompatible (:rewrite car-of-last-becomes-nth) (:rewrite nth-of-len-minus-1-becomes-car-of-last)))

;; Tweaked to match std
(defthm last-of-cons
  (equal (last (cons a x))
         (if (consp x)
             (last x)
           (cons a x)))
  :hints (("Goal" :in-theory (enable last))))

(defthm last-when-not-consp-cheap
  (implies (not (consp l))
           (equal (last l)
                  l))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable last))))

;; Also in books/std/lists/last.lisp?
(defthm consp-of-last
  (equal (consp (last l))
         (consp l))
  :hints (("Goal" :in-theory (enable last))))

(defthm last-iff
  (iff (last l)
       l))

(defthm len-of-last
  (equal (len (last l))
         (if (consp l)
             1
           0))
  :hints (("Goal" :in-theory (enable last))))

(defthm <=-of-acl2-count-of-last-linear
  (<= (acl2-count (last x))
      (acl2-count x))
  :rule-classes :linear)

(defthm <-of-acl2-count-of-last-linear
  (implies (< 1 (len x))
           (< (acl2-count (last x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm last-when-not-cdr-cheap
  (implies (not (cdr x))
           (equal (last x)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))
