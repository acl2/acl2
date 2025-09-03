; A lightweight book about the built-in function update-nth.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Make the var names in these rules more uniform, but note that the
;; first formal of update-nth is named KEY rather than N for some reason, so
;; consider not following our usual convention where we match the names of the
;; formals as much as possible.

(local (include-book "append"))

(in-theory (disable update-nth))

;; Note that the rule len-update-nth is built in to ACL2.  However, this rule
;; seems better, because here the case split is essentially on (< n (len x)),
;; which we will often know to be true.  By contrast, in len-update-nth, the
;; case split is essentially on (> (+ 1 n) (len x)).  The rule
;; len-of-update-nth from STD seems even worse, as it causes an unnecessary
;; case split on whether n is equal to one less than the length.
(defthm len-of-update-nth-2 ; avoid name conflict with STD
  (equal (len (update-nth n val x))
         (if (< (nfix n) (len x))
             (len x)
           (+ 1 (nfix n)))))
(in-theory (disable len-update-nth))

;; Avoids a case split
(defthm <-of-len-of-update-nth
  (implies (natp n)
           (< n (len (update-nth n val l))))
  :hints (("Goal" :in-theory (enable update-nth nfix))))

;; Match what's in STD
(defthm update-nth-of-update-nth-same
  (equal (update-nth n v1 (update-nth n v2 x))
         (update-nth n v1 x))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm car-of-update-nth
  ;; [Jared] changed variable names for compatibility with std/lists
  (equal (car (update-nth n v x))
         (if (zp n)
             v
           (car x)))
  :hints (("Goal" :in-theory (enable update-nth))))

;same as in std
(defthm update-nth-of-update-nth-diff
  (implies (not (equal (nfix n1) (nfix n2)))
           (equal (update-nth n1 v1 (update-nth n2 v2 x))
                  (update-nth n2 v2 (update-nth n1 v1 x))))
  :rule-classes ((:rewrite :loop-stopper ((n1 n2 update-nth))))
  :hints (("Goal" :in-theory (enable update-nth))))

;; If the value is the same, it doesn't matter whether the indices are the same or different.
(defthm update-nth-of-update-nth-same-val
  (equal (update-nth n1 v (update-nth n2 v x))
         (update-nth n2 v (update-nth n1 v x)))
  :rule-classes ((:rewrite :loop-stopper ((n1 n2 update-nth))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthmd update-nth-when-equal-of-nth
  (implies (and (equal val (nth n lst))
                (natp n)
                (< n (len lst)))
           (equal (update-nth n val lst)
                  lst))
  :hints (("Goal" :in-theory (enable update-nth))))

;rename
(defthm cdr-of-update-nth-0
  (equal (cdr (update-nth 0 v lst))
         (cdr lst))
  :hints (("Goal" :in-theory (enable update-nth))))

;dup with jvm/jvm-facts.lisp
(defthm cdr-of-update-nth
  ;; [Jared] renamed variables for compatibility with std/lists/update-nth
  (equal (cdr (update-nth n v x))
         (if (zp n)
             (cdr x)
           (update-nth (1- n) v (cdr x))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm update-nth-of-cons
  ;; [Jared] renamed variables for compatibility with the same rule
  ;; from std/lists/update-nth
  (equal (update-nth n x (cons a b))
         (if (zp n)
             (cons x b)
           (cons a (update-nth (1- n) x b)))))

(defthm true-list-fix-of-update-nth-2
  (equal (true-list-fix (update-nth key val l))
         (update-nth key val (true-list-fix l)))
  :hints (("Goal" :in-theory (enable update-nth))))

;todo dup?
(defthm take-update-nth
  (implies (and (integerp n)
                ;; (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (take n (update-nth n2 v l))
                  (if (<= n n2)
                      (take n l)
                      (update-nth n2 v (take n l)))))
  :hints (("Goal" :in-theory (enable take update-nth))))

;; Often we'll know (true-listp l) and no case split will occur.
;; Not quite the same as true-listp-of-update-nth in std.
;; Note that a related rule, true-listp-update-nth, is built-in but is a :type-prescription rule.
(defthm true-listp-of-update-nth-2
  (equal (true-listp (update-nth key val l))
         (if (true-listp l)
             t
           (not (< (nfix key) (len l)))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm update-nth-0-equal-rewrite
  (equal (equal (update-nth 0 v1 lst)
                (cons v2 rst))
         (and (equal v1 v2)
              (equal (cdr lst)
                     rst))))

(defthm equal-of-update-nth-same
  (implies (natp n)
           (equal (equal x (update-nth n val x))
                  (and (< n (len x))
                       (equal val (nth n x)))))
  :hints (("Goal" :in-theory (enable update-nth))))

;rename to nth-of-update-nth-safe
(defthmd nth-update-nth-safe
  (implies (and (syntaxp (quotep m))
                (syntaxp (quotep n)))
           (equal (nth m (update-nth n val l))
                  (if (equal (nfix m) (nfix n))
                      val (nth m l))))
  :hints (("Goal" :in-theory (enable nth))))

;matches std except has one less nfix
(defthm nthcdr-of-update-nth-simpler
  (equal (nthcdr n1 (update-nth n2 val x))
         (if (< (nfix n2) (nfix n1))
             (nthcdr n1 x)
           (update-nth (- n2 (nfix n1)) val (nthcdr n1 x))))
  :hints (("Goal" ;:induct (sub1-sub1-cdr-induct n key l)
           :expand (update-nth n2 val (nthcdr (+ -1 n1) (cdr x)))
           :in-theory (enable update-nth nthcdr))))

(defthm nthcdr-of-update-nth-when-<
  (implies (and (< n2 n1)
                (natp n2)
                (natp n1))
           (equal (nthcdr n1 (update-nth n2 val list))
                  (nthcdr n1 list)))
  :hints (("Goal" :in-theory (enable update-nth nthcdr))))

(defthm update-nth-of-append
  (equal (update-nth n val (append x y))
         (if (< (nfix n) (len x))
             (append (update-nth n val x) y)
           (append x (update-nth (- n (len x)) val y))))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(local
 (defun sub1-cdr-cdr-induct (n x y)
  (if (zp n)
      (list n x y)
    (sub1-cdr-cdr-induct (+ -1 n) (cdr x) (cdr y)))))

(defthmd equal-of-update-nth-new
  (implies (natp n)
           (equal (equal y (update-nth n val x))
                  (and (<= (+ 1 n) (len y))
                       (equal (nth n y) val)
                       (equal (take n y)
                              (take n x))
                       (equal (nthcdr (+ 1 n) x)
                              (nthcdr (+ 1 n) y)))))
  :hints (("Goal" :induct (sub1-cdr-cdr-induct n x y)
           :in-theory (enable update-nth))))

(defthm update-nth-of-take-of-+-of-1-same
  (implies (and (<= (len lst) n)
                (integerp n))
           (equal (update-nth n val (take (+ 1 n) lst))
                  (update-nth n val lst)))
  :hints (("Goal" :induct t
           :in-theory (enable update-nth))))

;; rename?
;; Kept disabled by default.
(defthmd update-nth-rw
  (implies (and (natp n)
                (< n (len lst)))
           (equal (update-nth n val lst)
                  (append (take n lst)
                          (list val)
                          (nthcdr (+ 1 n) lst)))))

;; updating one past the end
(defthm update-nth-becomes-append
  (implies (equal key (len lst))
           (equal (update-nth key val lst)
                  (append lst (list val))))
  :hints (("Goal" :in-theory (enable true-listp))))
