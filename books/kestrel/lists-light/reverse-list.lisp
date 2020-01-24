; A lightweight book about reverse-list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book introduces REVERSE-LIST, a simple function to reverse a list,
;; along with several theorems about it.

(local (include-book "append"))
(local (include-book "nth"))
(local (include-book "take"))
(local (include-book "nthcdr"))
(local (include-book "true-list-fix"))
(local (include-book "no-duplicatesp-equal"))

;; TODO: Consider replacing REVERSE-LIST with REV from books/std.  But note
;; that REVERSE-LIST has a stricter guard that prevents errors, such as calling
;; it on a string, that REV will silently allow.  Also, REVERSE-LIST is simpler
;; than REV (no auxiliary REVAPPEND-WITHOUT-GUARD function).  An approach could
;; be to simply rewrite REVERSE-LIST to REV during reasoning, or perhaps to
;; define REVERSE-LIST to call REV (once the definition of REV is untangled
;; from the other stuff in books/std/lists).

(local (in-theory (disable reverse revappend)))

;; In the logic, this is the nice recursive version of reverse, but it has a
;; fast executable body. Unlike REVERSE, this doesn't deal with strings, only
;; lists.
(defund reverse-list (x)
  (declare (xargs :guard (true-listp x)
                  :verify-guards nil ;done below
                  ))
  (mbe :logic (if (consp x)
                  (append (reverse-list (cdr x)) (list (car x)))
                nil)
       :exec (revappend x nil)))

;enable?
(defthmd revappend-lemma
  (equal (revappend x acc)
         (append (reverse-list x)
                 acc))
  :hints (("Goal" :in-theory (enable reverse-list revappend append))))

(verify-guards reverse-list :hints (("Goal" :expand ((reverse-list x))
                                     :do-not '(generalize eliminate-destructors)
                                     :in-theory (e/d (revappend-lemma) (append-of-nil-arg2)))))

;; Reasoning should be done about reverse-list, not reverse, when possible.
(defthm reverse-becomes-reverse-list
  (implies (true-listp x) ;rules out strings
           (equal (reverse x)
                  (reverse-list x)))
  :hints (("Goal" :in-theory (enable reverse reverse-list revappend-lemma))))

(defthm true-listp-of-reverse-list
  (true-listp (reverse-list x))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm reverse-list-iff
  (iff (reverse-list y)
       (consp y))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm len-of-reverse-list
  (equal (len (reverse-list y))
         (len y))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm consp-of-reverse-list
  (equal (consp (reverse-list x))
         (consp x))
  :hints (("Goal" :in-theory (enable reverse-list))))

;maybe drop since we open endp?
(defthm endp-of-reverse-list
  (equal (endp (reverse-list x))
         (endp x))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm reverse-list-of-append
  (equal (reverse-list (append x y))
         (append (reverse-list y) (reverse-list x)))
  :hints (("Goal" :in-theory (enable reverse-list append))))

(defthm reverse-list-of-reverse-list
  (equal (reverse-list (reverse-list x))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable reverse-list append))))

(defthm reverse-list-of-cons
  (equal (reverse-list (cons a x))
         (append (reverse-list x)
                 (list a)))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm car-of-reverse-list
  (equal (car (reverse-list x))
         (nth (+ -1 (len x)) x))
  :hints (("Goal" :in-theory (enable reverse-list append))))

(defthmd car-of-reverse-list-2
  (equal (car (reverse-list x))
         (car (last x))))

(defthm reverse-list-of-true-list-fix
  (equal (reverse-list (true-list-fix x))
         (reverse-list x))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm member-equal-of-reverse-list-iff
  (iff (member-equal x (reverse-list y))
       (member-equal x y))
  :hints (("Goal" :in-theory (enable reverse-list))))

(local
 (defthm nth-of-reverse-list-simple
   (implies (and (natp n)
                 (< n (len x))
                 )
            (equal (nth n (reverse-list x))
                   (nth (+ -1 (len x) (- (nfix n))) x)))
   :hints (("Goal" :in-theory (e/d (reverse-list nth) (nth-of-cdr))))))

(local
 (defthm nth-of-reverse-list-helper
   (implies (natp n)
            (equal (nth n (reverse-list x))
                   (if (< n (len x))
                       (nth (+ -1 (len x) (- (nfix n))) x)
                     nil)))
   :hints (("Goal" :in-theory (enable NTH-WHEN-<=-LEN)))))

(defthm nth-of-reverse-list
  (equal (nth n (reverse-list x))
         (if (< (nfix n) (len x))
             (nth (+ -1 (len x) (- (nfix n))) x)
           nil)))

(defthm cdr-of-reverse-list
  (equal (cdr (reverse-list lst))
         (reverse-list (take (+ -1 (len lst)) lst)))
  :hints (("Goal" :in-theory (enable reverse-list take))))

(defthm last-of-reverse-list
  (equal (last (reverse-list x))
         (if (consp x)
             (list (car x))
           nil))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm take-of-reverse-list
  (implies (and (<= n (len x))
                (natp n))
           (equal (take n (reverse-list x))
                  (reverse-list (nthcdr (- (len x) n) x))))
  :hints (("Goal" :in-theory (enable reverse-list nthcdr))))

(defthm butlast-of-reverse-list
  (equal (butlast (reverse-list x) n)
         (reverse-list (nthcdr n x)))
  :hints (("Goal" :in-theory (enable butlast reverse-list nthcdr))))

(defthm nthcdr-of-reverse-list
  (implies (and (<= n (len x))
                (natp n))
           (equal (nthcdr n (reverse-list x))
                  (reverse-list (take (- (len x) n) x))))
  :hints (("Goal" :in-theory (enable nthcdr reverse-list))))

(defthmd equal-of-reverse-list
  (equal (equal x (reverse-list y))
         (and (true-listp x)
              (equal (true-list-fix y) (reverse-list x))))
  :hints (("Goal" :use (:instance reverse-list-of-true-list-fix (x y))
           :in-theory (disable reverse-list-of-true-list-fix))))

(defthm equal-of-reverse-list-and-reverse-list
  (equal (equal (reverse-list x)
                (reverse-list y))
         (equal (true-list-fix x)
                (true-list-fix y)))
  :hints (("Goal" :use (:instance equal-of-reverse-list (x (reverse-list x))))))

(defthm intersection-equal-of-reverse-list-arg1-iff
  (iff (intersection-equal (reverse-list x) y)
       (intersection-equal x y)))

(defthm intersection-equal-of-reverse-list-arg2
  (equal (intersection-equal x (reverse-list y))
         (intersection-equal x y)))

(defthm no-duplicatesp-equal-of-reverse-list
  (equal (no-duplicatesp-equal (reverse-list x))
         (no-duplicatesp-equal x))
  :hints (("Goal" :in-theory (enable reverse-list))))
