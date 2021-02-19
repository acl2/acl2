; A lightweight book about the built-in function nthcdr.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "cdr"))
(local (include-book "len"))

(in-theory (disable nthcdr))

(defthm nthcdr-of-cons
  (equal (nthcdr n (cons a x))
         (if (zp n)
             (cons a x)
           (nthcdr (+ -1 n) x)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-nil
  (equal (nthcdr n nil)
         nil)
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-0
  (equal (nthcdr 0 x)
         x)
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-when-not-posp
  (implies (not (posp n))
           (equal (nthcdr n x)
                  x))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-when-not-consp-cheap
  (implies (not (consp x))
           (equal (nthcdr n x)
                  (if (zp n)
                      x
                    nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;same as in std
(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (nfix (- (len l) (nfix n))))
  :hints (("Goal" :in-theory (enable zp nthcdr))))

(defthm acl2-count-of-nthcdr-weak-linear
  (<= (acl2-count (nthcdr n x))
      (acl2-count x))
  :rule-classes ((:linear :trigger-terms ((acl2-count (nthcdr n x)))))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm acl2-count-of-nthcdr-strong-linear
  (implies (and (consp x)
                (posp n))
           (< (acl2-count (nthcdr n x))
              (acl2-count x)))
  :rule-classes ((:linear :trigger-terms ((acl2-count (nthcdr n x))))))

(defthm nthcdr-iff
  (iff (nthcdr n x)
       (if (< (nfix n) (len x))
           t
         (if (equal (nfix n) (len x))
             ;; If we know true-listp, this simplifies to nil and get merged
             ;; with the nil branch below.
             (not (true-listp x))
           nil)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(local
 (defthmd not-equal-when-<-of-lens
   (implies (< (len y) (len x))
            (not (equal x y)))))

(defthm equal-of-nthcdr-same
  (equal (equal x (nthcdr n x))
         (or (zp n)
             (not x)))
  :hints (("Goal" :in-theory (enable nthcdr))
          ("subgoal *1/2"
           :use (:instance not-equal-when-<-of-lens (y (nthcdr (+ -1 n) (cdr x)))))))

(defthm nthcdr-when-equal-of-len
  (implies (and (equal (len x) k) ; k is a free var
                (syntaxp (quotep k))
                (<= k n)
                (true-listp x) ;could drop but then we need finalcdr
                (integerp n)
                (natp k))
           (equal (nthcdr n x)
                  nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(local
 (defthm integerp-of-one-less
   (equal (integerp (+ -1 n))
          (or (not (acl2-numberp n))
              (integerp n)))
   :hints (("Goal" :cases ((integerp n))))))

(defthm consp-of-nthcdr
  (equal (consp (nthcdr n x))
         (< (nfix n) (len x)))
  :hints (("Subgoal *1/2" :cases ((< n (+ 1 (len (cdr x))))))
          ("Subgoal *1/1" :cases ((consp x)))
          ("Goal" :in-theory (enable nthcdr))))

(defthmd cdr-of-nthcdr
  (equal (cdr (nthcdr n x))
         (nthcdr (+ 1 (nfix n)) x))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthmd nthcdr-opener-alt
  (implies (not (zp n))
           (equal (nthcdr n l)
                  (cdr (nthcdr (+ -1 n) l))))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthmd nthcdr-opener-alt2
  (implies (and (< n (len l))
                (natp n))
           (equal (nthcdr n l)
                  (cons (nth n l)
                        (nthcdr (+ 1 n) l))))
  :hints (("goal" :induct (nthcdr n l)
           :in-theory (enable zp nthcdr))))

;rename?
(defthmd nthcdr-of-+-opener
  (implies (and (syntaxp (quotep k))
                (posp k)
                (natp n))
           (equal (nthcdr (+ k n) x)
                  (cdr (nthcdr (+ (+ -1 k) n) x))))
  :hints (("Goal" :in-theory (enable cdr-of-nthcdr))))

(theory-invariant (incompatible (:rewrite nthcdr-of-+-opener)
                                (:rewrite cdr-of-nthcdr)))

;same as in std
(defthm car-of-nthcdr
  (equal (car (nthcdr i x))
         (nth i x))
  :hints (("Goal" :use (:instance nthcdr-opener-alt2
                                  (n (nfix n))))))

;same as in std
(defthm nth-of-nthcdr
  (equal (nth n (nthcdr m x))
         (nth (+ (nfix n) (nfix m)) x))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-true-list-fix
  ;; [Jared] renamed variables for compatibility with std/lists/nthcdr.lisp
  (equal (nthcdr n (true-list-fix x))
         (true-list-fix (nthcdr n x)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthmd true-list-fix-of-nthcdr
  (equal (true-list-fix (nthcdr n x))
         (nthcdr n (true-list-fix x))))

(theory-invariant (incompatible (:rewrite true-list-fix-of-nthcdr) (:rewrite nthcdr-of-true-list-fix)))



;todo: think about this
(defthmd 3-cdrs
  (equal (cdr (cdr (cdr lst)))
         (nthcdr 3 lst)))

(defthm nthcdr-of-1
  (equal (nthcdr 1 lst)
         (cdr lst))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm equal-of-len-of-nthcdr-and-len
  (implies (and (<= n (len x))
                (natp n))
           (equal (equal (len (nthcdr n x)) (len x))
                  (zp n))))

;more general than nthcdr-of-append in books/kestrel/utilities/lists/nthcdr-theorems.lisp
(defthm nthcdr-of-append-gen
  (equal (nthcdr n (append x y))
         (if (<= (len x) (nfix n))
             (nthcdr (- n (len x)) y)
           (append (nthcdr n x)
                   y)))
  :hints (("Goal" :in-theory (enable nthcdr append))))

;There is already an NTHCDR-OF-CDR in std/lists/nthcdr.lisp.
(defthm nthcdr-of-cdr-combine
  (implies (natp n)
           (equal (nthcdr n (cdr lst))
                  (nthcdr (+ 1 n) lst)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-cdr-combine-strong
  (equal (nthcdr n (cdr lst))
         (if (natp n)
             (nthcdr (+ 1 n) lst)
           (cdr lst)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; The above may loop with (:definition nthcdr) ?

;; The unfortunate param names here are to match std
(defthm nthcdr-of-nthcdr
  (equal (nthcdr a (nthcdr b x))
         (nthcdr (+ (nfix a) (nfix b)) x))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthmd cdr-of-cdr-becomes-nthcdr
  (equal (cdr (cdr x))
         (nthcdr 2 x))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthmd nthcdr-when-<-of-len
  (implies (< (len x) (nfix n))
           (equal (nthcdr n x)
                  nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; Often we'll know (true-listp x) and no case split will occur.
;; Not quite the same as true-listp-of-nthcdr in std.
(defthm true-listp-of-nthcdr-2
  (equal (true-listp (nthcdr n x))
         (if (true-listp x)
             t
           (< (len x) (nfix n))))
  :hints (("Subgoal *1/5" :cases ((< (len x) n)))
          ("Goal"
           :in-theory (e/d (nthcdr)
                           (nthcdr-of-cdr-combine-strong
                            nthcdr-of-cdr-combine)))))

(defthm true-listp-of-nthcdr-3
  (equal (true-listp (nthcdr n x))
         (if (<= (nfix n) (len x))
             (true-listp x)
           t)))
