; A lightweight book about the built-in function strip-cdrs.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable strip-cdrs))

(defthm consp-of-strip-cdrs
  (equal (consp (strip-cdrs x))
         (consp x))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-iff
  (iff (strip-cdrs x)
       (consp x))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm len-of-strip-cdrs
  (equal (len (strip-cdrs x))
         (len x))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-cons
  (equal (strip-cdrs (cons a x))
         (cons (cdr a)
               (strip-cdrs x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-acons
  (equal (strip-cdrs (acons key datum alist))
         (cons datum
               (strip-cdrs alist)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm car-of-strip-cdrs
  (equal (car (strip-cdrs x))
         (cdr (car x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm cadr-of-strip-cdrs
  (equal (cadr (strip-cdrs x))
         (cdr (cadr x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

;; Not sure which is better
(defthmd strip-cdrs-of-cdr
  (equal (strip-cdrs (cdr x))
         (cdr (strip-cdrs x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm nth-of-strip-cdrs
  (equal (nth n (strip-cdrs x))
         (cdr (nth n x)))
  :hints (("Goal" :in-theory (enable nth strip-cdrs))))

(defthm strip-cdrs-of-append
  (equal (strip-cdrs (append x y))
         (append (strip-cdrs x)
                 (strip-cdrs y)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-pairlis$-when-equal-lengths
  (implies (equal (len x) (len y))
           (equal (strip-cdrs (pairlis$ x y))
                  (true-list-fix y)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

;; Also in pairlis-dollar.lisp
;compatible with std
(defthm strip-cdrs-of-pairlis$
  (equal (strip-cdrs (pairlis$ x y))
         (take (len x) y))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-revappend
  (equal (strip-cdrs (revappend x y))
         (revappend (strip-cdrs x)
                    (strip-cdrs y)))
  :hints (("Goal" :in-theory (enable strip-cdrs revappend))))

(defthm strip-cdrs-of-reverse
  (equal (strip-cdrs (reverse x))
         (reverse (strip-cdrs x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm <=-of-acl2-count-of-strip-cdrs-linear
  (<= (acl2-count (strip-cdrs x))
      (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable strip-cdrs))))
