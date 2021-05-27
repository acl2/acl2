; A generic mergesort function and some proofs about it
;
; Copyright (C) 2018-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "split-list-fast")
(include-book "kestrel/lists-light/perm-def" :dir :system)
(local (include-book "kestrel/lists-light/perm2" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (enable revappend-lemma)))

;; ;todo: use remove1?
;; (defthm remove-1-of-true-list-fix
;;   (equal (bag::remove-1 a (true-list-fix x))
;;          (bag::remove-1 a x)))

;; (defthm remove-1-of-append-when-memberp
;;   (implies (list::memberp a x)
;;            (equal (bag::remove-1 a (append x y))
;;                   (append (bag::remove-1 a x) (true-list-fix y))))
;;   :hints (("Goal" :in-theory (enable append))))

;; (defcong perm perm (append x y) 1 :hints (("Goal" :in-theory (enable append))))

;; (defcong perm perm (append x y) 2 :hints (("Goal" :in-theory (enable append))))

(defthm perm-of-remove-1-of-car-and-append-same
  (perm (remove1$ (car x) (append y x))
        (if (consp x)
            (append y (cdr x))
          (remove1$ nil y)))
  :hints (("Goal" :in-theory (enable append))))

;dup
(defthm len-of-cdr-better
  (equal (len (cdr x))
         (if (equal 0 (len x))
             0
           (+ -1 (len x)))))

(in-theory (disable len))
;add theory invar?

;; (defthm my-memberp-of-append ;this must exist
;;   (equal (list::memberp a (append x y))
;;          (or (list::memberp a x)
;;              (list::memberp a y))))

;move
(defthm perm-of-append-of-mv-nth-0-of-split-list-fast-aux-and-mv-nth-1-of-split-list-fast-aux
  (implies (<= (len tail) (len lst))
           (perm (append (mv-nth 0 (split-list-fast-aux lst tail acc))
                              (mv-nth 1 (split-list-fast-aux lst tail acc)))
                 (append lst acc)))
;  :hints (("Goal" :expand ((APPEND ACC LST))))
)

(defthm perm-of-append-of-mv-nth-0-of-split-list-fast-and-mv-nth-1-of-split-list-fast
  (perm (append (mv-nth 0 (split-list-fast x))
                     (mv-nth 1 (split-list-fast x)))
             x)
  :hints (("Goal" :in-theory (enable split-list-fast))))

;; A generic predicate with a guard of t.  Should we constrain this to be boolean?
(encapsulate ( ((generic-predp *) => * :formals (x) :guard t))
  (local (defun generic-predp (x) x)))

;(defforall-simple generic-predp)
;(verify-guards all-generic-predp)
(defund all-generic-predp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (generic-predp (first x))
         (all-generic-predp (rest x)))))

(defthm generic-predp-of-car
  (implies (and (all-generic-predp x)
                (consp x))
           (generic-predp (car x)))
  :hints (("Goal" :in-theory (enable all-generic-predp))))

(defthm all-generic-predp-of-cdr
  (implies (all-generic-predp x)
           (all-generic-predp (cdr x)))
  :hints (("Goal" :in-theory (enable all-generic-predp))))

(defthm all-generic-predp-of-cons
  (equal (all-generic-predp (cons x y))
         (and (generic-predp x)
              (all-generic-predp y)))
  :hints (("Goal" :in-theory (enable all-generic-predp))))

(defthm all-generic-predp-of-append
  (equal (all-generic-predp (append x y))
         (and (all-generic-predp x)
              (all-generic-predp y)))
  :hints (("Goal" :in-theory (enable all-generic-predp))))

(defthm all-generic-predp-of-revappend
  (equal (all-generic-predp (revappend x y))
         (and (all-generic-predp x)
              (all-generic-predp y)))
  :hints (("Goal" :in-theory (enable all-generic-predp))))




;; A generic comparision function with a guard that requires both arguments
;; satisfy generic-predp.  Should we constrain this to be boolean?
(encapsulate (((generic-comparison * *) => * :formals (x y) :guard (and (generic-predp x) (generic-predp y))))
  (local (defun generic-comparison (x y) (list x y))))

(defun merge-generic (l1 l2 acc)
  (declare (xargs :measure (+ (len l1) (len l2))
                  :hints
                  (("Goal"
                    :in-theory
                    (union-theories '(o-p o-finp o< len-of-cdr-better
                                          (:compound-recognizer natp-compound-recognizer)
                                          (:type-prescription len)
                                          consp-when-len-equal-constant
                                          )
                                    (theory 'minimal-theory))))
                  :guard (and (all-generic-predp l1)
                              (all-generic-predp l2)
                              (true-listp acc))))
  (cond ((atom l1) (revappend acc l2))
        ((atom l2) (revappend acc l1))
        ((generic-comparison (car l1) (car l2))
         (merge-generic (cdr l1) l2 (cons (car l1) acc)))
        (t (merge-generic l1 (cdr l2) (cons (car l2) acc)))))

(defun merge-sort-generic (l)
  (declare (xargs :measure (len l)
                  :hints
                  (("Goal"
                    :in-theory
                    (union-theories '(o-p o-finp o< len-of-cdr-better
                                          (:compound-recognizer natp-compound-recognizer)
                                          (:type-prescription len)
                                          ;;consp-when-len-equal-constant
                                          len-of-split-list-fast-bound2
                                          len-of-split-list-fast-bound)
                                    (theory 'minimal-theory))))
                  :guard (and (true-listp l) (all-generic-predp l))
                  :verify-guards nil ;done below
                  ))
  (if (atom (cdr l))
      l
      (mv-let (first-half second-half)
        (split-list-fast l)
        (merge-generic (merge-sort-generic first-half)
                                  (merge-sort-generic second-half)
                                  nil))))

(defthm all-generic-predp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-generic-predp lst)
                (all-generic-predp acc)
                (<= (len tail) (len lst)))
           (all-generic-predp (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable generic-predp-of-car))))

(defthm all-generic-predp-of-mv-nth-0-of-split-list-fast
  (implies (all-generic-predp lst)
           (all-generic-predp (mv-nth 0 (split-list-fast lst))))
  :hints
  (("Goal" :use (:instance all-generic-predp-of-mv-nth-0-of-split-list-fast-aux
                           (tail lst)
                           (acc nil))
    :in-theory '(split-list-fast all-generic-predp))))

(defthm all-generic-predp-of-mv-nth-1-of-split-list-fast-aux
  (implies (all-generic-predp lst)
           (all-generic-predp (mv-nth 1 (split-list-fast-aux lst tail acc)))))

(defthm all-generic-predp-of-mv-nth-1-of-split-list-fast
  (implies (all-generic-predp lst)
           (all-generic-predp (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-generic-predp-of-merge-generic
  (implies (and (all-generic-predp l1)
                (all-generic-predp l2)
                (all-generic-predp acc))
           (all-generic-predp (merge-generic l1 l2 acc)))
  :hints (("Goal" :in-theory '(merge-generic all-generic-predp-of-cdr
                                                        all-generic-predp-of-cons
                                                        all-generic-predp-of-revappend
                                                        generic-predp-of-car
                                                        atom))))

(defthm all-generic-predp-of-merge-sort-generic
  (implies (all-generic-predp lst)
           (all-generic-predp (merge-sort-generic lst))))

(verify-guards merge-sort-generic
  :hints (("Goal" :induct (merge-sort-generic l))))

(defthm true-listp-of-merge-generic
  (implies (and (true-listp l1) (true-listp l2))
           (true-listp (merge-generic l1 l2 acc)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable merge-sort-generic))))

(defthm true-listp-of-merge-sort-generic
  (implies (true-listp lst)
           (true-listp (merge-sort-generic lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable merge-sort-generic))))

(verify-guards merge-sort-generic)

(defthm perm-of-merge-generic
  (perm (merge-generic x y acc)
        (append x y acc))
  :hints (("Goal" :induct (merge-generic x y acc))))

(defthm perm-of-merge-sort-generic
  (perm (merge-sort-generic x)
        x))
