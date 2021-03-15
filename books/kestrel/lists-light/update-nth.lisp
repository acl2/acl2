; A lightweight book about the built-in function update-nth.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable update-nth))

;; Match what's in STD
(defthm update-nth-of-update-nth-same
  (equal (update-nth n v1 (update-nth n v2 x))
         (update-nth n v1 x))
  :hints (("Goal" :in-theory (enable update-nth))))

;BOZO add to update-nth library?
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
  :hints (("Goal" :in-theory (enable UPDATE-NTH))))

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
  :hints (("Goal" :in-theory (e/d (;repeat
                                   update-nth)
                                  (;list::list-equiv-hack
                                   )))))

;todo dup?
(defthm take-update-nth
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (take n (update-nth n2 v l))
                  (if (<= n n2)
                      (take n l)
                      (update-nth n2 v (take n l)))))
  :hints
  (("Goal" :in-theory (enable TAKE; repeat
                              update-nth))))

;; Often we'll know (true-listp l) and no case split will occur.
;; Not quite the same as true-listp-of-update-nth in std.
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
