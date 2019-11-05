; A lightweight book about the built-in function binary-append.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "cons"))
(local (include-book "take"))
(local (include-book "nthcdr"))

(in-theory (disable append))

;; Note that append has a built-in :type-prescription rule, true-listp-append.

(defthm car-of-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y)))
  :hints (("Goal" :in-theory (enable append))))

;; same as in std/lists/append.lisp
(defthm cdr-of-append
  (equal (cdr (append x y))
         (if (consp x)
             (append (cdr x) y)
           (cdr y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm len-of-append
  (equal (len (append x y))
         (+ (len x) (len y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-nil-arg1
  (equal (append nil y)
         y)
  :hints (("Goal" :in-theory (enable append))))

(defthmd append-when-not-consp-arg1
  (implies (not (consp x))
           (equal (append x y)
                  y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (equal (append x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-nil-arg2
  (equal (append x nil)
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable append))))

(defthm true-listp-of-append
  (equal (true-listp (append x y))
         (true-listp y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-associative
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable append))))

(defthm consp-of-append
  (equal (consp (append x y))
         (or (consp x)
             (consp y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-cons-arg1
  (equal (append (cons a x) y)
         (cons a (append x y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm true-list-fix-of-append
  (equal (true-list-fix (append x y))
         (append x (true-list-fix y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-iff
  (iff (append x y)
       (or (consp x)
           y))
  :hints (("Goal" :in-theory (enable append))))

(local
 (defthmd not-equal-when-lens-not-equal
   (implies (not (equal (len x) (len y)))
            (not (equal x y)))))

(defthm equal-of-append-same-arg2
  (equal (equal y (append x y))
         (not (consp x)))
  :hints (("Goal" :expand (append x y)
           :in-theory (enable not-equal-when-lens-not-equal))))

(defthm equal-of-append-and-append-same-arg1
  (equal (equal (append x y) (append x z))
         (equal y z))
  :hints (("Goal" :in-theory (enable append))))

(defthm nthcdr-of-len-and-append
  (equal (nthcdr (len x) (append x y))
         y)
  :hints (("Goal" :in-theory (enable append nthcdr))))

(defthm take-of-len-and-append
  (equal (take (len x) (append x y))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable append nthcdr))))

(defthm append-of-true-list-fix-arg1
  (equal (append (true-list-fix x) y)
         (append x y)))

; a fairly aggressive rule.  when enabling this, consider also including the
; books about take and nthcdr.
(defthmd equal-of-append
  (equal (equal x (append y z))
         (and (<= (len y) (len x)) ;this might not be needed if we used firstn instead of take
              (equal (take (len y) x)
                     (true-list-fix y))
              (equal (nthcdr (len y) x)
                     z)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance append-of-true-list-fix-arg1
                            (x y)
                            (y (NTHCDR (LEN Y) X)))
                 (:instance append-of-take-and-nthcdr-2
                            (n (len y))
                            (l x)))
           :in-theory (e/d (nthcdr-when-<-of-len)
                           (append-of-true-list-fix-arg1
                            append-of-take-and-nthcdr-2)))))

(defthm equal-of-append-and-append-when-equal-of-len-and-len
  (implies (equal (len x1) (len x2))
           (equal (equal (append x1 y1) (append x2 y2))
                  (and (equal (true-list-fix x1)
                              (true-list-fix x2))
                       (equal y1 y2))))
  :hints (("Goal" :in-theory (enable equal-of-append))))

;; Improved to match std
(defthm last-of-append
  (equal (last (append x y))
         (if (consp y)
             (last y)
           (append (last x) y)))
  :hints (("Goal" :in-theory (enable last append))))
