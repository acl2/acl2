; Support for finding probable facts in DAGs.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")
(include-book "test-cases")
;(include-book "evaluator") ; for apply-axe-evaluator ; todo: use basic eval but need to evaluate dag-val-with-axe-evaluator in examples like rc4-loop, make this file a generator that takes an evaluator?
(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove
(include-book "kestrel/bv/bvif" :dir :system) ; do not remove
(include-book "kestrel/typed-lists-light/minelem" :dir :system) ; todo: include just the def?
(include-book "kestrel/typed-lists-light/nat-list-listp" :dir :system)
(include-book "kestrel/alists-light/acons-all-to-val" :dir :system)
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "numeric-lists"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-lists" :dir :system))

(local (in-theory (e/d (true-listp-of-cdr-strong)
                       (true-listp-of-cdr))))


(local (in-theory (disable append mv-nth strip-cars natp)))

(local (in-theory (enable true-listp-when-nat-listp-rewrite)))

(local
 (defthm natp-of-car-of-car
   (implies (and (nat-listp (strip-cars alist))
                 (consp alist))
            (natp (car (car alist))))
   :hints (("Goal" :in-theory (enable strip-cars)))))

(local
 (defthm <-of-car-of-car
   (implies (and (all-< (strip-cars alist) bound)
                 (consp alist))
            (< (car (car alist)) bound))
   :hints (("Goal" :in-theory (enable strip-cars)))))

;dup
(local
 (defthm strip-cars-of-cons
   (equal (strip-cars (cons a x))
          (cons (car a)
                (strip-cars x)))
   :hints (("Goal" :in-theory (enable strip-cars)))))


(local
 (defthm strip-cars-of-cdr
   (equal (strip-cars (cdr x))
          (cdr (strip-cars x)))
   :hints (("Goal" :in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm all-consp-of-array-to-alist-aux
;;   (implies (all-consp acc)
;;            (all-consp (array-to-alist-aux n len array-name array acc)))
;;   :hints (("Goal" :in-theory (enable array-to-alist-aux))))

;; (defthm all-consp-of-array-to-alist
;;   (all-consp (array-to-alist array-name array len))
;;   :hints (("Goal" :in-theory (enable array-to-alist))))

;; (defthm nat-listp-of-strip-cars-of-array-to-alist-aux
;;   (implies (nat-listp (strip-cars acc))
;;            (nat-listp (strip-cars (array-to-alist-aux n len array-name array acc))))
;;   :hints (("Goal" :in-theory (enable array-to-alist-aux))))

;; (defthm nat-listp-of-strip-cars-of-array-to-alist
;;   (nat-listp (strip-cars (array-to-alist array-name array len)))
;;   :hints (("Goal" :in-theory (enable array-to-alist))))

;; (defthm all-<-of-strip-cars-of-array-to-alist-aux
;;   (implies (and (all-< (strip-cars acc) bound)
;;                 (<= len bound))
;;            (all-< (strip-cars (array-to-alist-aux n len array-name array acc)) bound))
;;   :hints (("Goal" :in-theory (enable array-to-alist-aux))))

;; (defthm all-<-of-strip-cars-of-array-to-alist
;;   (implies (<= len bound)
;;            (all-< (strip-cars (array-to-alist array-name array len)) bound))
;;   :hints (("Goal" :in-theory (enable array-to-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm nat-listp-of-strip-cars-of-cdr
   (implies (nat-listp (strip-cars x))
            (nat-listp (strip-cars (cdr x))))))

(local
 (defthm nat-listp-of-reverse-list
   (implies (nat-listp x)
            (nat-listp (reverse-list x)))
   :hints (("Goal" :in-theory (enable reverse-list nat-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;make local?
(defthm nat-listp-of-lookup-equal
  (implies (nat-list-listp (strip-cdrs alist))
           (nat-listp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs
                                     nat-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund all-all-< (x bound)
  (declare (xargs :guard (and (nat-list-listp x) ;gen?
                              (rationalp bound))
                  :guard-hints (("Goal" :in-theory (enable nat-list-listp)))))
  (if (endp x)
      t
    (and (all-< (first x) bound)
         (all-all-< (rest x) bound))))

(defthm all-all-<-of-nil
  (all-all-< nil bound)
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-<-of-car-when-all-all-<
  (implies (and (all-all-< x bound)
                (consp x))
           (all-< (car x) bound))
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-all-<-of-cons
  (equal (all-all-< (cons a x) bound)
         (and (all-< a bound)
              (all-all-< x bound)))
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-all-<-of-append
  (equal (all-all-< (append x y) bound)
         (and (all-all-< x bound)
              (all-all-< y bound)))
  :hints (("Goal" :in-theory (enable all-all-< append))))

(defthm all-<-of-lookup-equal
  (implies (all-all-< (strip-cdrs alist) bound)
           (all-< (lookup-equal key alist) bound))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs
                                     all-all-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; comparison function for the sort
(defun-inline lexorder-of-cdrs (x y)
  (declare (xargs :guard (and (consp x)
                              (consp y))))
  (lexorder (cdr x) (cdr y)))

;; todo: pass in a list-pred (a kind of alist)?
(defmergesort merge-sort-lexorder-of-cdrs
  merge-lexorder-of-cdrs
  lexorder-of-cdrs
  consp)

(local
 (defthmd alistp-when-all-consp
   (implies (all-consp x)
            (equal (alistp x)
                   (true-listp x)))
   :hints (("Goal" :in-theory (enable alistp)))))

(local
 (defthmd alistp-becomes-all-consp
   (equal (alistp x)
          (and (all-consp x)
               (true-listp x)))
   :hints (("Goal" :in-theory (enable alistp)))))

;; (defthm alistp-of-merge-lexorder-of-cdrs
;;   (implies (and (alistp l1)
;;                 (alistp l2)
;;                 (alistp acc))
;;            (alistp (merge-lexorder-of-cdrs l1 l2 acc)))
;;   :hints (("Goal" :in-theory (enable merge-lexorder-of-cdrs))))

(defthm alistp-of-merge-sort-lexorder-of-cdrs
  (implies (alistp l)
           (alistp (merge-sort-lexorder-of-cdrs l)))
  :hints (("Goal" :in-theory (enable merge-sort-lexorder-of-cdrs alistp-becomes-all-consp))))

(defthm nat-listp-of-strip-cars-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (nat-listp (strip-cars lst))
                (nat-listp (strip-cars acc))
                (<= (len tail) (len lst)))
           (nat-listp (strip-cars (mv-nth 0 (split-list-fast-aux lst tail acc)))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm nat-listp-of-strip-cars-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (nat-listp (strip-cars lst))
                (nat-listp (strip-cars acc))
                (<= (len tail) (len lst)))
           (nat-listp (strip-cars (mv-nth 1 (split-list-fast-aux lst tail acc)))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm nat-listp-of-strip-cars-of-mv-nth-0-of-split-list-fast
  (implies (nat-listp (strip-cars lst))
           (nat-listp (strip-cars (mv-nth 0 (split-list-fast lst)))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm nat-listp-of-strip-cars-of-mv-nth-1-of-split-list-fast
  (implies (nat-listp (strip-cars lst))
           (nat-listp (strip-cars (mv-nth 1 (split-list-fast lst)))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm nat-listp-of-strip-cars-of-merge-lexorder-of-cdrs
  (implies (and (nat-listp (strip-cars l1))
                (nat-listp (strip-cars l2))
                (nat-listp (strip-cars acc)))
           (nat-listp (strip-cars (merge-lexorder-of-cdrs l1 l2 acc))))
  :hints (("Goal" :in-theory (enable merge-lexorder-of-cdrs))))

(defthm nat-listp-of-strip-cars-of-merge-sort-lexorder-of-cdrs
  (implies (nat-listp (strip-cars lst))
           (nat-listp (strip-cars (merge-sort-lexorder-of-cdrs lst))))
  :hints (("Goal" :in-theory (enable merge-sort-lexorder-of-cdrs))))

(defthm all-<-of-strip-cars-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-< (strip-cars lst) bound)
                (all-< (strip-cars acc) bound)
                (<= (len tail) (len lst)))
           (all-< (strip-cars (mv-nth 0 (split-list-fast-aux lst tail acc)))
                  bound))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm all-<-of-strip-cars-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (all-< (strip-cars lst) bound)
                (all-< (strip-cars acc) bound)
                (<= (len tail) (len lst)))
           (all-< (strip-cars (mv-nth 1 (split-list-fast-aux lst tail acc)))
                   bound))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm all-<-of-strip-cars-of-mv-nth-0-of-split-list-fast
  (implies (all-< (strip-cars lst) bound)
           (all-< (strip-cars (mv-nth 0 (split-list-fast lst))) bound))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-<-of-strip-cars-of-mv-nth-1-of-split-list-fast
  (implies (all-< (strip-cars lst) bound)
           (all-< (strip-cars (mv-nth 1 (split-list-fast lst))) bound))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-<-of-strip-cars-of-merge-lexorder-of-cdrs
  (implies (and (all-< (strip-cars l1) bound)
                (all-< (strip-cars l2) bound)
                (all-< (strip-cars acc) bound))
           (all-< (strip-cars (merge-lexorder-of-cdrs l1 l2 acc))
                   bound))
  :hints (("Goal" :in-theory (enable merge-lexorder-of-cdrs))))

(defthm all-<-of-strip-cars-of-merge-sort-lexorder-of-cdrs
  (implies (all-< (strip-cars lst) bound)
           (all-< (strip-cars (merge-sort-lexorder-of-cdrs lst)) bound))
  :hints (("Goal" :in-theory (enable merge-sort-lexorder-of-cdrs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm nat-listp-of-mv-nth-0-of-split-list-fast-aux
;;   (implies (and (nat-listp lst)
;;                 (nat-listp acc)
;;                 (<= (len tail) (len lst)))
;;            (nat-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm nat-listp-of-mv-nth-1-of-split-list-fast-aux
;;   (implies (and (nat-listp lst)
;;                 (nat-listp acc)
;;                 (<= (len tail) (len lst)))
;;            (nat-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm nat-listp-of-mv-nth-0-of-split-list-fast
;;   (implies (nat-listp lst)
;;            (nat-listp (mv-nth 0 (split-list-fast lst))))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm nat-listp-of-mv-nth-1-of-split-list-fast
;;   (implies (nat-listp lst)
;;            (nat-listp (mv-nth 1 (split-list-fast lst))))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm nat-listp-of-merge-<
;;   (implies (and (nat-listp l1)
;;                 (nat-listp l2)
;;                 (nat-listp acc))
;;            (nat-listp (merge-< l1 l2 acc)))
;;   :hints (("Goal" :in-theory (enable merge-<))))

;; (defthm nat-listp-of-merge-sort-<
;;   (implies (nat-listp lst)
;;            (nat-listp (merge-sort-< lst)))
;;   :hints (("Goal" :in-theory (enable merge-sort-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm all-<-of-mv-nth-0-of-split-list-fast-aux
;;   (implies (and (all-< lst bound)
;;                 (all-< acc bound)
;;                 (<= (len tail) (len lst)))
;;            (all-< (mv-nth 0 (split-list-fast-aux lst tail acc))
;;                   bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm all-<-of-mv-nth-1-of-split-list-fast-aux
;;   (implies (and (all-< lst bound)
;;                 (all-< acc bound)
;;                 (<= (len tail) (len lst)))
;;            (all-< (mv-nth 1 (split-list-fast-aux lst tail acc))
;;                    bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm all-<-of-mv-nth-0-of-split-list-fast
;;   (implies (all-< lst bound)
;;            (all-< (mv-nth 0 (split-list-fast lst)) bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm all-<-of-mv-nth-1-of-split-list-fast
;;   (implies (all-< lst bound)
;;            (all-< (mv-nth 1 (split-list-fast lst)) bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm all-<-of-merge-<
;;   (implies (and (all-< l1 bound)
;;                 (all-< l2 bound)
;;                 (all-< acc bound))
;;            (all-< (merge-< l1 l2 acc)
;;                    bound))
;;   :hints (("Goal" :in-theory (enable merge-<))))

;; (defthm all-<-of-merge-sort-<
;;   (implies (all-< lst bound)
;;            (all-< (merge-sort-< lst) bound))
;;   :hints (("Goal" :in-theory (enable merge-sort-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defund num-true-nodes (n array-name array)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (not (natp n))
;;       0
;;       (if (aref1 array-name array n)
;;           (+ 1
;;              (num-true-nodes (+ -1 n) array-name array))
;;         (num-true-nodes (+ -1 n) array-name array))))

;; (defthm <=-of-num-true-nodes-linear
;;   (implies (and (integerp n)
;;                 (<= -1 n))
;;            (<= (num-true-nodes n array-name array)
;;                (+ 1 n)))
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable num-true-nodes))))

;; (defthm num-true-nodes-of-aset1
;;   (implies (and (array1p array-name array)
;;                 (natp n)
;;                 (< n (alen1 array-name array))
;;                 (natp index)
;;                 (<= index n)
;;                 val)
;;            (equal (num-true-nodes n array-name (aset1 array-name array index val))
;;                   (if (aref1 array-name array index)
;;                       (num-true-nodes n array-name array)
;;                     (+ 1 (num-true-nodes n array-name array)))))
;;   :hints (("Goal" :expand ((num-true-nodes 0 array-name (aset1 array-name array 0 val))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Looks for an initial segment of NODE-TO-VALUE-ALIST all of whose vals are VALUE.
;; Returns (mv entries-with-value remaining-node-to-value-alist).
(defund leading-entries-with-value (node-to-value-alist value acc)
  (declare (xargs :guard (and (alistp node-to-value-alist)
                              (nat-listp (strip-cars node-to-value-alist))
                              (nat-listp acc))))
  (if (endp node-to-value-alist)
      (mv acc node-to-value-alist)
    (let* ((entry (car node-to-value-alist))
           (nodenum (car entry))
           (this-value (cdr entry)))
      (if (equal this-value value)
          (leading-entries-with-value (cdr node-to-value-alist) value (cons nodenum acc))
        ;; stop looking, since the entries are sorted by value and we found a difference:
        (mv acc node-to-value-alist)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-leading-entries-with-value
   (implies (and (nat-listp (strip-cars node-to-value-alist))
                 (nat-listp acc))
            (nat-listp (mv-nth 0 (leading-entries-with-value node-to-value-alist value acc))))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm all-<-of-mv-nth-0-of-leading-entries-with-value
   (implies (and (all-< (strip-cars node-to-value-alist) bound)
                 (all-< acc bound)
                 )
            (all-< (mv-nth 0 (leading-entries-with-value node-to-value-alist value acc)) bound))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm <=-of-len-of-mv-nth-1-of-leading-entries-with-value
   (<= (len (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc)))
       (len node-to-value-alist))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-leading-entries-with-value
   (implies (nat-listp (strip-cars node-to-value-alist))
            (nat-listp (strip-cars (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc)))))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm alistp-of-strip-cars-of-mv-nth-1-of-leading-entries-with-value
   (implies (alistp node-to-value-alist)
            (alistp (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc))))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-leading-entries-with-value
   (implies (and (all-< (strip-cars node-to-value-alist) bound)
                 (all-< acc bound)
                 )
            (all-< (strip-cars (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc))) bound))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm true-listp-of-mv-nth-1-of-leading-entries-with-value
   (implies (alistp node-to-value-alist)
            (true-listp (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc))))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

(local
 (defthm consp-of-mv-nth-1-of-leading-entries-with-value
   (implies (alistp node-to-value-alist)
            (iff (consp (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc)))
                 (mv-nth 1 (leading-entries-with-value node-to-value-alist value acc))))
   :hints (("Goal" :in-theory (enable leading-entries-with-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv probably-equal-node-sets singleton-count probably-constant-node-alist).
(defund initial-probable-facts-aux (node-to-value-alist ; grouped so that each group of nodes with the same val forms a contiguous block, should have no :unused nodes
                                    ;; accumulators:
                                    probably-equal-node-sets
                                    singleton-count
                                    probably-constant-node-alist)
  (declare (xargs :guard (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                              (nat-listp (strip-cars node-to-value-alist))
                              (nat-list-listp probably-equal-node-sets)
                              (natp singleton-count)
                              (alistp probably-constant-node-alist))
                  :guard-hints (("Goal" :in-theory (enable (:d strip-cars))))
                  :measure (len node-to-value-alist)))
  (if (atom node-to-value-alist)
      (mv probably-equal-node-sets singleton-count probably-constant-node-alist)
    (b* ((entry (first node-to-value-alist))
         (nodenum (car entry))
         (value (cdr entry))
         ;; Gather all immediately following nodes with the same value:
         ((mv equiv-set node-to-value-alist)
          (leading-entries-with-value (rest node-to-value-alist) value nil))
         ((mv probably-equal-node-sets singleton-count)
          (if equiv-set ; there's at least one other node with the same value
              (mv (cons (cons nodenum equiv-set) probably-equal-node-sets) singleton-count)
            ;; only NODENUM has the value VALUE, so it is a singleton:
            (mv probably-equal-node-sets (+ 1 singleton-count))))
         ;; NODENUM and all nodes in EQUIV-SET are candidates for always being equal to the constant VALUE:
         (probably-constant-node-alist
           (acons-fast nodenum value (acons-all-to-val equiv-set value probably-constant-node-alist))))
      (initial-probable-facts-aux node-to-value-alist ; we've already moved past at least one entry
                                  probably-equal-node-sets
                                  singleton-count
                                  probably-constant-node-alist))))

(defthm initial-probable-facts-aux-return-type
  (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                (nat-listp (strip-cars node-to-value-alist))
                (nat-list-listp probably-equal-node-sets)
                (all-consp probably-equal-node-sets) ; no empty sets (in fact, there can't be singletons either)
                (natp singleton-count)
                (alistp probably-constant-node-alist)
                (nat-listp (strip-cars probably-constant-node-alist)))
           (and (nat-list-listp (mv-nth 0 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist)))
                (all-consp (mv-nth 0 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist)))
                (natp (mv-nth 1 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist)))
                (alistp (mv-nth 2 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist)))
                (nat-listp (strip-cars (mv-nth 2 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist))))
                (nat-listp (mv-nth 3 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist)))))
  :hints (("Goal" :in-theory (enable initial-probable-facts-aux))))

(defthm initial-probable-facts-aux-return-type-with-bound
  (implies (and (all-all-< probably-equal-node-sets bound)
                (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                (nat-listp (strip-cars node-to-value-alist))
                (all-< (strip-cars node-to-value-alist) bound)
                (nat-list-listp probably-equal-node-sets)
                (natp singleton-count)
                (alistp probably-constant-node-alist)
                (all-< (strip-cars probably-constant-node-alist)
                       bound))
           (and (all-all-< (mv-nth 0 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist))
                           bound)
                (all-< (strip-cars (mv-nth 2 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist)))
                       bound)
                (all-< (mv-nth 3 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist))
                       bound)))
  :hints (("Goal" :in-theory (enable initial-probable-facts-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (local
;;  (defthm all-<-of-mv-nth-0-of-initial-probable-constants
;;    (implies (and (natp nodenum)
;;                  (natp miter-len)
;;                  (array1p test-case-array-name test-case-array)
;;                  (<= miter-len (alen1 test-case-array-name test-case-array))
;;                  (nat-listp never-used-nodes)
;;                  (ALL-< NEVER-USED-NODES MITER-LEN)
;;                  (alistp probably-constant-node-alist))
;;             (all-< (mv-nth 0 (initial-probable-constants nodenum
;;                                                          miter-len
;;                                                          test-case-array-name test-case-array
;;                                                          never-used-nodes
;;                                                          probably-constant-node-alist))
;;                    miter-len))
;;    :hints (("Goal" :in-theory (enable initial-probable-constants)))))

;; (local
;;  (defthm nat-listp-of-mv-nth-0-of-initial-probable-constants
;;    (implies (and (natp nodenum)
;;                  (natp miter-len)
;;                  (array1p test-case-array-name test-case-array)
;;                  (<= miter-len (alen1 test-case-array-name test-case-array))
;;                  (nat-listp never-used-nodes)
;;                  (ALL-< NEVER-USED-NODES MITER-LEN)
;;                  (alistp probably-constant-node-alist))
;;             (nat-listp (mv-nth 0 (initial-probable-constants nodenum
;;                                                              miter-len
;;                                                              test-case-array-name test-case-array
;;                                                              never-used-nodes
;;                                                              probably-constant-node-alist))))
;;    :hints (("Goal" :in-theory (enable initial-probable-constants)))))

;; (local
;;  (defthm alistp-of-mv-nth-1-of-initial-probable-constants
;;    (implies (and (natp nodenum)
;;                  (natp miter-len)
;;                  (array1p test-case-array-name test-case-array)
;;                  (<= miter-len (alen1 test-case-array-name test-case-array))
;;                  (nat-listp never-used-nodes)
;;                  (alistp probably-constant-node-alist))
;;             (alistp (mv-nth 1 (initial-probable-constants nodenum
;;                                                           miter-len
;;                                                           test-case-array-name test-case-array
;;                                                           never-used-nodes
;;                                                           probably-constant-node-alist))))
;;    :hints (("Goal" :in-theory (enable initial-probable-constants)))))

;; (local
;;  (defthm all-<-of-strip-cars-of-mv-nth-1-of-initial-probable-constants
;;    (implies (and (natp nodenum)
;;                  (natp miter-len)
;;                  (array1p test-case-array-name test-case-array)
;;                  (<= miter-len (alen1 test-case-array-name test-case-array))
;;                  (nat-listp never-used-nodes)
;;                  (alistp probably-constant-node-alist)
;;                  (all-< (strip-cars probably-constant-node-alist) miter-len))
;;             (all-< (strip-cars (mv-nth 1 (initial-probable-constants nodenum
;;                                                                      miter-len
;;                                                                      test-case-array-name test-case-array
;;                                                                      never-used-nodes
;;                                                                      probably-constant-node-alist)))
;;                    miter-len))
;;    :hints (("Goal" :in-theory (enable initial-probable-constants)))))

;; (local
;;  (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-initial-probable-constants
;;    (implies (and (natp nodenum)
;;                  (natp miter-len)
;;                  (array1p test-case-array-name test-case-array)
;;                  (<= miter-len (alen1 test-case-array-name test-case-array))
;;                  (nat-listp never-used-nodes)
;;                  (alistp probably-constant-node-alist)
;;                  (all-< (strip-cars probably-constant-node-alist) miter-len)
;;                  (NAT-LISTP (STRIP-CARS PROBABLY-CONSTANT-NODE-ALIST)))
;;             (nat-listp (strip-cars (mv-nth 1 (initial-probable-constants nodenum
;;                                                                          miter-len
;;                                                                          test-case-array-name test-case-array
;;                                                                          never-used-nodes
;;                                                                          probably-constant-node-alist)))))
;;    :hints (("Goal" :in-theory (enable initial-probable-constants)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns (mv non-singletons singleton-count).
;; (defund drop-and-count-singletons (lst non-singletons-acc count-acc)
;;   (declare (xargs :guard (and (integerp count-acc)
;;                               (true-listp lst))))
;;   (if (endp lst)
;;       (mv non-singletons-acc count-acc)
;;     (let* ((item (car lst)))
;;       (if (and (consp item) ; drop if all are known to be non empty lists?
;;                (not (consp (cdr item))))
;;           ;; it's a singleton, so drop it and count it:
;;           (drop-and-count-singletons (cdr lst) non-singletons-acc (+ 1 count-acc))
;;         ;; it's not a singleton, so keep it:
;;         (drop-and-count-singletons (cdr lst) (cons item non-singletons-acc) count-acc)))))

;; (local
;;  (defthm true-listp-of-mv-nth-0-of-drop-and-count-singletons
;;    (implies (true-listp acc)
;;             (true-listp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
;;    :hints (("Goal" :in-theory (enable drop-and-count-singletons)))))

;; (local
;;  (defthm nat-list-listp-of-mv-nth-0-of-drop-and-count-singletons
;;    (implies (and (nat-list-listp acc)
;;                  (nat-list-listp lst))
;;             (nat-list-listp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
;;    :hints (("Goal" :in-theory (enable drop-and-count-singletons
;;                                       nat-list-listp)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-drop-and-count-singletons
;;    (implies (and (all-consp acc)
;;                  (all-consp lst)
;;                  )
;;             (all-consp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
;;    :hints (("Goal" :in-theory (enable drop-and-count-singletons
;;                                       nat-list-listp)))))

;; (local
;;  (defthm all-all-<-of-mv-nth-0-of-drop-and-count-singletons
;;    (implies (and (all-all-< acc bound)
;;                  (all-all-< lst bound)
;;                  )
;;             (all-all-< (mv-nth 0 (drop-and-count-singletons lst acc count-acc))
;;                        bound))
;;    :hints (("Goal" :in-theory (enable drop-and-count-singletons
;;                                       nat-list-listp
;;                                       all-all-<)))))

;; (local
;;  (defthm natp-mv-nth-1-of-drop-and-count-singletons
;;    (implies (natp count-acc)
;;             (natp (mv-nth 1 (drop-and-count-singletons lst acc count-acc))))
;;    :rule-classes :type-prescription
;;    :hints (("Goal" :in-theory (enable drop-and-count-singletons)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;ignores later pairs that bind already-bound keys
;; (defund strip-cdrs-unique (lst keys-seen acc)
;;   (declare (xargs :guard (and (alistp lst)
;;                               (true-listp keys-seen))))
;;   (if (endp lst)
;;       acc ;we don't bother to reverse this
;;     (let* ((entry (car lst))
;;            (key (car entry)))
;;       (if (member-equal key keys-seen)
;;           (strip-cdrs-unique (cdr lst) keys-seen acc)
;;         (strip-cdrs-unique (cdr lst) (cons key keys-seen) (cons (cdr entry) acc))))))

;; (local
;;  (defthm true-listp-of-strip-cdrs-unique
;;    (implies (true-listp acc)
;;             (true-listp (strip-cdrs-unique lst keys-seen acc)))
;;    :hints (("Goal" :in-theory (enable strip-cdrs-unique)))))

;; (local
;;  (defthm nat-list-listp-of-strip-cdrs-unique
;;    (implies (and (nat-list-listp acc)
;;                  (nat-list-listp (strip-cdrs lst)))
;;             (nat-list-listp (strip-cdrs-unique lst keys-seen acc)))
;;    :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp)))))

;; (local
;;  (defthm all-consp-of-strip-cdrs-unique
;;    (implies (and (all-consp acc)
;;                  (all-consp (strip-cdrs lst)))
;;             (all-consp (strip-cdrs-unique lst keys-seen acc)))
;;    :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp)))))

;; (local
;;  (defthm all-all-<-of-strip-cdrs-unique
;;    (implies (and (all-all-< acc bound)
;;                  (all-all-< (strip-cdrs lst) bound))
;;             (all-all-< (strip-cdrs-unique lst keys-seen acc) bound))
;;    :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp all-all-<)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;;we first make an alist whose keys are data values (often 0 or 1?) and whose vals are sets of nodenums
;; ;returns (mv new-sets new-singleton-count)
;; (defund split-set (set test-case-array-name test-case-array)
;;   (declare (xargs :guard (and (nat-listp set)
;;                               (array1p test-case-array-name test-case-array)
;;                               (all-< set (alen1 test-case-array-name test-case-array)))))
;;   (let* ((alist (test-case-alist-for-set set test-case-array-name test-case-array nil)) ;this could be slow?  better to pair nodenums with vals and merge-sort the pairs by value?
;;          (new-node-sets (strip-cdrs-unique alist nil nil)) ;don't cons this up?
;;          )
;;     ;;fixme combine this with the work above:
;;     (drop-and-count-singletons new-node-sets nil 0)))

;; (local
;;  (defthm true-listp-of-mv-nth-0-of-split-set
;;    (true-listp (mv-nth 0 (split-set set test-case-array-name test-case-array)))
;;    :hints (("Goal" :in-theory (enable split-set)))))

;; (local
;;  (defthm nat-list-listp-of-mv-nth-0-of-split-set
;;    (implies (and (nat-listp set)
;;                  (array1p test-case-array-name test-case-array)
;;                  (all-< set (alen1 test-case-array-name test-case-array)))
;;             (nat-list-listp (mv-nth 0 (split-set set test-case-array-name test-case-array))))
;;    :hints (("Goal" :in-theory (enable split-set)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-split-set
;;    (implies (and (nat-listp set)
;;                  (array1p test-case-array-name test-case-array)
;;                  (all-< set (alen1 test-case-array-name test-case-array)))
;;             (all-consp (mv-nth 0 (split-set set test-case-array-name test-case-array))))
;;    :hints (("Goal" :in-theory (enable split-set)))))

;; (local
;;  (defthm all-all-<-of-mv-nth-0-of-split-set
;;    (implies (and (nat-listp set)
;;                  (array1p test-case-array-name test-case-array)
;;                  (all-< set (alen1 test-case-array-name test-case-array))
;;                  (<= (alen1 test-case-array-name test-case-array) bound))
;;             (all-all-< (mv-nth 0 (split-set set test-case-array-name test-case-array))
;;                        bound))
;;    :hints (("Goal" :in-theory (enable split-set)))))

;; (local
;;  (defthm natp-of-mv-nth-1-of-split-set
;;    (natp (mv-nth 1 (split-set set test-case-array-name test-case-array)))
;;    :rule-classes :type-prescription
;;    :hints (("Goal" :in-theory (enable split-set)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splits the grouped-alist.
;; Returns (mv extended-acc singleton-count).
(defund group-nodes-by-value (node-to-value-alist ; grouped so that each group of nodes with the same val forms a contiguous block, should have no :unused nodes
                              ;; accumulators:
                              acc ; the probably-equal-node-sets
                              singleton-count)
  (declare (xargs :guard (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                              (nat-listp (strip-cars node-to-value-alist))
                              (nat-list-listp acc)
                              (natp singleton-count))
                  :measure (len node-to-value-alist)))
  (if (endp node-to-value-alist)
      (mv acc singleton-count)
    (b* ((entry (first node-to-value-alist))
         (nodenum (car entry))
         (value (cdr entry))
         ;; Gather all immediately following nodes with the same value:
         ((mv equiv-set node-to-value-alist)
          (leading-entries-with-value (rest node-to-value-alist) value nil))
         ((mv acc singleton-count)
          (if equiv-set ; there's at least one other node with the same value
              (mv (cons (cons nodenum equiv-set) acc) singleton-count)
            ;; only NODENUM has the value VALUE, so it is a singleton:
            (mv acc (+ 1 singleton-count)))))
      (group-nodes-by-value node-to-value-alist ; we've already moved past at least one entry
                            acc
                            singleton-count))))

(defthm nat-list-listp-of-mv-nth-0-of-group-nodes-by-value
  (implies (and (alistp node-to-value-alist)
                (nat-listp (strip-cars node-to-value-alist))
                (nat-list-listp acc)
                (natp singleton-count))
           (nat-list-listp (mv-nth 0 (group-nodes-by-value node-to-value-alist acc singleton-count))))
  :hints (("Goal" :in-theory (enable group-nodes-by-value))))

(defthm all-consp-of-mv-nth-0-of-group-nodes-by-value
  (implies (and (alistp node-to-value-alist)
                (nat-listp (strip-cars node-to-value-alist))
                (all-consp acc)
                (natp singleton-count))
           (all-consp (mv-nth 0 (group-nodes-by-value node-to-value-alist acc singleton-count))))
  :hints (("Goal" :in-theory (enable group-nodes-by-value))))

(defthm all-all-<-of-mv-nth-0-of-group-nodes-by-value
  (implies (and (alistp node-to-value-alist)
                (nat-listp (strip-cars node-to-value-alist))
                (all-< (strip-cars node-to-value-alist) bound)
                (all-all-< acc bound)
                (natp singleton-count))
           (all-all-< (mv-nth 0 (group-nodes-by-value node-to-value-alist acc singleton-count)) bound))
  :hints (("Goal" :in-theory (enable group-nodes-by-value))))

(defthm natp-of-mv-nth-1-of-group-nodes-by-value
  (implies (natp singleton-count)
           (natp (mv-nth 1 (group-nodes-by-value node-to-value-alist acc singleton-count))))
  :hints (("Goal" :in-theory (enable group-nodes-by-value))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (local
;;  (defthm all-all-<-of-mv-nth-0-of-group-same-entries
;;    (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
;;                  (nat-listp (strip-cars node-to-value-alist))
;;                  (all-< (strip-cars node-to-value-alist) bound)
;;                  (nat-list-listp acc)
;;                  (all-all-< acc bound)
;;                  (natp singleton-count))
;;             (all-all-< (mv-nth 0 (group-same-entries node-to-value-alist acc singleton-count)) bound))
;;    :hints (("Goal" :in-theory (enable group-same-entries)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-group-same-entries
;;    (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
;;                  (nat-listp (strip-cars node-to-value-alist))
;;                  (nat-list-listp acc)
;;                  (all-consp acc)
;;                  (natp singleton-count))
;;             (all-consp (mv-nth 0 (group-same-entries node-to-value-alist acc singleton-count))))
;;    :hints (("Goal" :in-theory (enable group-same-entries)))))

;; (local
;;  (defthm nat-list-listp-of-mv-nth-0-of-group-same-entries
;;    (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
;;                  (nat-listp (strip-cars node-to-value-alist))
;;                  (nat-list-listp acc)
;;                  (all-consp acc)
;;                  (natp singleton-count))
;;             (nat-list-listp (mv-nth 0 (group-same-entries node-to-value-alist acc singleton-count))))
;;    :hints (("Goal" :in-theory (enable group-same-entries)))))

;; (local
;;  (defthm natp-of-mv-nth-1-of-group-same-entries
;;    (implies (natp singleton-count)
;;             (natp (mv-nth 1 (group-same-entries node-to-value-alist acc singleton-count))))
;;    :hints (("Goal" :in-theory (enable group-same-entries)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-set-of-unused-nodes (probably-equal-node-sets never-used-nodes acc)
  (declare (xargs :guard (and (nat-list-listp probably-equal-node-sets)
                              (nat-listp never-used-nodes)
                              (nat-list-listp acc))))
  (if (endp probably-equal-node-sets)
      acc ; todo: error?
    (let* ((set (first probably-equal-node-sets))
           (one-nodenum (first set)))
      (if (member one-nodenum never-used-nodes)
          ;;drop this set (and stop looking):
          (append (cdr probably-equal-node-sets) acc)
        (remove-set-of-unused-nodes (rest probably-equal-node-sets) never-used-nodes (cons set acc))))))

(defthm nat-list-listp-of-remove-set-of-unused-nodes
  (implies (and (nat-list-listp acc)
                (nat-list-listp probably-equal-node-sets))
           (nat-list-listp (remove-set-of-unused-nodes probably-equal-node-sets never-used-nodes acc)))
  :hints (("Goal" :in-theory (enable REMOVE-SET-OF-UNUSED-NODES))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun <-of-mins (x y)
  (declare (xargs :guard (and (nat-listp x)
                              ;; (consp x) ; todo members of the set should be non-empty
                              (nat-listp y)
                              ;; (consp y) ; todo
                              )
                  :guard-hints (("Goal" :in-theory (e/d (rationalp-when-natp) (natp))))))
  (< (if (atom x) 0 (minelem x))
     (if (atom y) 0 (minelem y))))

;; For sorting probably-equal-node-sets.
(defmergesort merge-sort-<-of-mins merge-<-of-mins <-of-mins nat-listp)

;; todo: why both notions?
;todo: localize
(defthmd all-nat-listp-when-nat-list-listp
  (implies (nat-list-listp x)
           (all-nat-listp x))
  :hints (("Goal" :in-theory (enable nat-list-listp all-nat-listp))))

(defund print-probable-info (all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist)
  (declare (xargs :guard (and (booleanp all-passedp)
                              (nat-list-listp probably-equal-node-sets)
                              (nat-listp never-used-nodes)
                              (alistp probably-constant-node-alist))))
  (progn$ (cw "All passed: ~x0.~%" all-passedp)
          (cw "~x0 probably-equal-node-sets: ~X12.~%" (len probably-equal-node-sets)
              (merge-sort-<-of-mins probably-equal-node-sets)
              nil)
          (cw "~x0 never-used-nodes: ~X12.~%" (len never-used-nodes) never-used-nodes nil)
          (cw "probably-constant-node-alist: ~x0.~%" probably-constant-node-alist)))
