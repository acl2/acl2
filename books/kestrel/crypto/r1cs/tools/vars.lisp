; Extracting variables from an R1CS
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "../sparse/r1cs")
(include-book "kestrel/utilities/split-list-fast-defs" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/utilities/split-list-fast" :dir :system))
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/strict-symbol-less-than-sortedp" :dir :system))

(local (in-theory (disable acl2::strip-cadrs evens odds)))

;move this stuff:

;todo
;; ;move
;; (thm
;;   (implies (symbol-listp x)
;;            (acl2::strict-symbol<-sortedp (acl2::merge-sort-symbol< x)))
;;   :hints (("Goal" :in-theory (enable acl2::merge-sort-symbol<))))

(local
 (defthm all->=-len-of-2-when-sparse-vectorp
   (implies (sparse-vectorp vec)
            (acl2::all->=-len vec 2))
   :hints (("Goal" :in-theory (enable sparse-vectorp
                                      acl2::all->=-len)))))

; move this stuff:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: factor out?

;lst1 and lst2 should be sorted in increasing order
;lst1 and lst2 should be duplicate-free
;acc is reverse-sorted and duplicate free
;result is sorted in increasing order and is duplicate-free
(defund merge-symbol<-and-remove-dups (lst1 lst2 acc)
  (declare (xargs :measure (+ 1 (len lst1) (len lst2))
                  :guard (and (symbol-listp lst1)
                              (symbol-listp lst2)
                              (symbol-listp acc))))
  (if (endp lst1)
      (revappend acc lst2)
    (if (endp lst2)
        (revappend acc lst1)
      (let ((item1 (first lst1))
            (item2 (first lst2)))
        (if (symbol< item1 item2)
            (merge-symbol<-and-remove-dups (rest lst1) lst2 (cons item1 acc))
          (if (symbol< item2 item1)
              (merge-symbol<-and-remove-dups lst1 (rest lst2) (cons item2 acc))
            ;; they are equal, so keep just one:
            (merge-symbol<-and-remove-dups (rest lst1) (rest lst2) (cons item1 acc))))))))

(defthm symbol-listp-of-merge-symbol<-and-remove-dups
  (implies (and (symbol-listp lst1)
                (symbol-listp lst2)
                (symbol-listp acc))
           (symbol-listp (merge-symbol<-and-remove-dups lst1 lst2 acc)))
  :hints (("Goal" :in-theory (enable merge-symbol<-and-remove-dups))))

;needed?
(local
  (defthmd not-symbol<-of-car-and-car-of-last
    (implies (and (acl2::strict-symbol<-sortedp (acl2::reverse-list x))
                  (symbol-listp x))
             (not (symbol< (car x)
                           (car (last x)))))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable acl2::strict-symbol<-sortedp acl2::reverse-list)))))

;; (defun symbol<= (sym1 sym2)
;;   (declare (xargs :guard (and (symbolp sym1)
;;                               (symbolp sym2))))
;;   (not (symbol< sym2 sym1)))

(defthm not-member-equal-when-strict-symbol<-sortedp-of-reverse-list-and-symbol<-car
  (implies (and (acl2::strict-symbol<-sortedp (acl2::reverse-list x))
                (symbol< (car x) a)
                (symbol-listp x))
           (not (member-equal a x)))
  :hints (("Goal" :in-theory (enable acl2::reverse-list))))

(defthm strict-symbol<-sortedp-of-merge-symbol<-and-remove-dups
  (implies (and (symbol-listp lst1)
                (symbol-listp lst2)
                (symbol-listp acc)
                (acl2::strict-symbol<-sortedp lst1)
                (acl2::strict-symbol<-sortedp lst2)
                (acl2::strict-symbol<-sortedp (acl2::reverse-list acc))
                (no-duplicatesp-equal lst1)
                (no-duplicatesp-equal lst2)
                (no-duplicatesp-equal acc)
                ;; acc has the smallest items:
                (implies (and (consp lst1) (consp acc))
                         (symbol< (car acc) (car lst1)))
                (implies (and (consp lst2) (consp acc))
                         (symbol< (car acc) (car lst2))))
           (acl2::strict-symbol<-sortedp (merge-symbol<-and-remove-dups lst1 lst2 acc)))
  :hints (("subgoal *1/2" :use (:instance not-symbol<-of-car-and-car-of-last (x acc)))
          ("Goal" :in-theory (enable acl2::strict-symbol<-sortedp
                                     merge-symbol<-and-remove-dups
                                     not-symbol<-of-car-and-car-of-last))))

;; todo: prove that strict-symbol<-sortedp implies no dups

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund r1cs-sparse-vector-vars (vec)
  (declare (xargs :guard (sparse-vectorp vec)))
  (remove-duplicates-equal ; or should we disallow duplicates?
   (remove '1 (acl2::strip-cadrs vec))))

;move?
(local
  (defthm symbol-listp-of-remove-equal-of-1-and-strip-cadrs-when-sparse-vectorp
    (implies (sparse-vectorp vec)
             (symbol-listp (remove-equal 1 (acl2::strip-cadrs vec))))
    :hints (("Goal" :in-theory (enable sparse-vectorp acl2::strip-cadrs)))))

(defthm symbol-listp-of-r1cs-sparse-vector-vars
  (implies (sparse-vectorp vec)
           (symbol-listp (r1cs-sparse-vector-vars vec)))
  :hints (("Goal" :in-theory (enable r1cs-sparse-vector-vars sparse-vectorp))))

(defthm no-duplicatesp-equal-of-r1cs-sparse-vector-vars
  (implies (sparse-vectorp vec)
           (no-duplicatesp-equal (r1cs-sparse-vector-vars vec)))
  :hints (("Goal" :in-theory (enable r1cs-sparse-vector-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund r1cs-constraint-vars (constraint)
  (declare (xargs :guard (r1cs-constraintp constraint)))
  (let ((a (r1cs-constraint->a constraint))
        (b (r1cs-constraint->b constraint))
        (c (r1cs-constraint->c constraint)))
    (union-eq (r1cs-sparse-vector-vars a)
              (r1cs-sparse-vector-vars b)
              (r1cs-sparse-vector-vars c))))

(defthm symbol-listp-of-r1cs-constraint-vars
  (implies (r1cs-constraintp constraint)
           (symbol-listp (r1cs-constraint-vars constraint)))
  :hints (("Goal" :in-theory (enable r1cs-constraint-vars))))

(defthm no-duplicatesp-equal-of-r1cs-constraint-vars
  (implies (r1cs-constraintp constraint)
           (no-duplicatesp-equal (r1cs-constraint-vars constraint)))
  :hints (("Goal" :in-theory (enable r1cs-constraint-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (progn
    (defthm r1cs-constraint-listp-of-mv-nth-0-of-split-list-fast-aux
      (implies (and (r1cs-constraint-listp acc)
                    (r1cs-constraint-listp lst)
                    (r1cs-constraint-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (r1cs-constraint-listp (mv-nth 0 (acl2::split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable acl2::split-list-fast-aux))))

    (defthm r1cs-constraint-listp-of-mv-nth-1-of-split-list-fast-aux
      (implies (and (r1cs-constraint-listp acc)
                    (r1cs-constraint-listp lst)
                    (r1cs-constraint-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (r1cs-constraint-listp (mv-nth 1 (acl2::split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable acl2::split-list-fast-aux))))

    (defthm r1cs-constraint-listp-of-mv-nth-0-of-split-list-fast
      (implies (r1cs-constraint-listp lst)
               (r1cs-constraint-listp (mv-nth 0 (acl2::split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable acl2::split-list-fast))))

    (defthm r1cs-constraint-listp-of-mv-nth-1-of-split-list-fast
      (implies (r1cs-constraint-listp lst)
               (r1cs-constraint-listp (mv-nth 1 (acl2::split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable acl2::split-list-fast))))))

;; Returns a list of symbols, sorted by symbol-<
(defund r1cs-constraint-list-vars (constraints)
  (declare (xargs :guard (r1cs-constraint-listp constraints)
                  :measure (len constraints)
                  :verify-guards nil ; done below
                  ))
  (if (endp constraints)
      nil
    (if (endp (rest constraints))
        ;; todo: use a faster sort (better list splitter):
        (acl2::merge-sort-symbol< (r1cs-constraint-vars (first constraints)))
      (mv-let (constraints1 constraints2)
        (acl2::split-list-fast constraints)
        (merge-symbol<-and-remove-dups (r1cs-constraint-list-vars constraints1)
                                       (r1cs-constraint-list-vars constraints2)
                                       nil)))))

(defthm symbol-listp-of-r1cs-constraint-list-vars
  (implies (r1cs-constraint-listp constraints)
           (symbol-listp (r1cs-constraint-list-vars constraints)))
  :hints (("Goal" :in-theory (enable r1cs-constraint-list-vars))))

;todo
;; (defthm no-duplicatesp-equal-of-r1cs-constraint-list-vars
;;   (implies (r1cs-constraint-listp constraints)
;;            (acl2::strict-symbol<-sortedp (r1cs-constraint-list-vars constraints)))
;;   :hints (("Goal" :in-theory (enable r1cs-constraint-list-vars))))

;todo
;; (defthm no-duplicatesp-equal-of-r1cs-constraint-list-vars
;;   (implies (r1cs-constraint-listp constraints)
;;            (no-duplicatesp-equal (r1cs-constraint-list-vars constraints)))
;;   :hints (("Goal" :in-theory (enable r1cs-constraint-list-vars))))

(verify-guards r1cs-constraint-list-vars)
