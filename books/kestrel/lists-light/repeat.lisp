; A lightweight book about repeat.
;
; Copyright (C) 2018-2019 Kestrel Institute
; See books/std/lists/list-defuns.lisp for the copyright on repeat itself.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book provides the repeat function from std/lists without bringing in
;; anything else from std/lists.  It also provides some theorems about repeat.

(local (include-book "cons"))
(local (include-book "nthcdr"))
(local (include-book "len"))

;; From books/std/lists/list-defuns.lisp:
(defund repeat (n x)
  (declare (xargs :guard (natp n)
                  :verify-guards nil ;; done below
                  ))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat (- n 1) x)))
       :exec (make-list n :initial-element x)))

;; See also |(repeat 0 x)| in std/lists/repeat
(defthm repeat-of-0
  (equal (repeat 0 x)
         nil)
  :hints (("Goal" :in-theory (enable repeat))))

(defthm repeat-iff
  (iff (repeat n x)
       (posp n))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm repeat-of-+-of-1
  (implies (and (syntaxp (not (quotep n))) ;defeat ACL2's overly aggressive matching
                (natp n))
           (equal (repeat (+ 1 n) x)
                  (cons x (repeat n x))))
  :hints (("Goal" :in-theory (enable repeat))))

;; Trying keeping this disabled.
(defthmd cons-onto-repeat
  (implies (natp n)
           (equal (cons v (repeat n v))
                  (repeat (+ 1 n) v)))
  :hints (("Goal" :in-theory (enable repeat))))

(theory-invariant (incompatible (:rewrite cons-onto-repeat) (:definition repeat)))
(theory-invariant (incompatible (:rewrite cons-onto-repeat) (:definition repeat-of-+-of-1)))

;; This can be viewed as an alternate definition of repeat that adds values at
;; the end.
(defthmd repeat-alt-def
  (implies (posp n)
           (equal (repeat n val)
                  (append (repeat (+ -1 n) val) (list val))))
  :hints (("Goal" :induct (repeat n val)
           :in-theory (enable repeat append))))

;matches std
(defthm repeat-when-zp
  (implies (zp n)
           (equal (repeat n a)
                  nil))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm make-list-ac-rewrite
  (equal (make-list-ac n val ac)
         (append (repeat n val) ac))
  :hints (("subGoal *1/2" :use (:instance repeat-alt-def)
           :in-theory (e/d () (repeat-alt-def)))))

(verify-guards repeat :hints (("Goal" :in-theory (enable repeat))))

(defthm len-of-repeat
  (equal (len (repeat n x))
         (nfix n))
  :hints (("Goal" :in-theory (enable repeat))))

;; the param name 'a' here is to match std
(defthm consp-of-repeat
  (equal (consp (repeat n a))
         (not (zp n)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm car-of-repeat
  (equal (car (repeat n x))
         (if (posp n)
             x
           nil))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm cdr-of-repeat
  (equal (cdr (repeat n x))
         (repeat (+ -1 n) x))
  :hints (("Goal" :in-theory (enable repeat))))

(local
 (defun sub1-sub1-induct (m n)
   (if (zp n)
       (list m n)
     (sub1-sub1-induct (+ -1 m) (+ -1 n)))))

;; the param name 'a' here is to match std
(defthm nth-of-repeat
  (equal (nth n (repeat m a))
         (if (< (nfix n) (nfix m))
             a
           nil))
  :hints (("Goal" :induct (sub1-sub1-induct m n)
           :in-theory (enable repeat nth))))

(defthmd repeat-opener-end
  (implies (posp n)
           (equal (repeat n v)
                  (append (repeat (+ -1 n) v) (list v))))
  :hints (("Goal" :in-theory (e/d (repeat append
                                   ) (CONS-ONTO-REPEAT
                                   zp-open
                                   )))))

;see the one in std/lists/repeat.lisp
(defthm my-nthcdr-of-repeat
  (equal (nthcdr n (repeat m x))
         (repeat (- (nfix m) (nfix n)) x))
  :hints (("Goal" :induct (sub1-sub1-induct m n)
           :in-theory (enable repeat))))

;drop?
(defthmd repeat-opener
  (implies (not (zp n))
           (equal (repeat n v)
                  (cons v (repeat (1- n) v)))))

(defthm equal-of-repeat-of-1
  (equal (equal (repeat 1 x) y)
         (and (true-listp y)
              (equal 1 (len y))
              (equal x (car y)))))

(defthm last-of-repeat
  (equal (last (repeat n x))
         (if (zp n)
             nil
           (list x)))
  :hints (("Goal" :in-theory (enable repeat))))
