; Finding likely facts to break down a proof
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
(include-book "evaluate-test-case")
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

(defthm all-consp-of-array-to-alist-aux
  (implies (all-consp acc)
           (all-consp (array-to-alist-aux n len array-name array acc)))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm all-consp-of-array-to-alist
  (all-consp (array-to-alist array-name array len))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm nat-listp-of-strip-cars-of-array-to-alist-aux
  (implies (nat-listp (strip-cars acc))
           (nat-listp (strip-cars (array-to-alist-aux n len array-name array acc))))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm nat-listp-of-strip-cars-of-array-to-alist
  (nat-listp (strip-cars (array-to-alist array-name array len)))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm all-<-of-strip-cars-of-array-to-alist-aux
  (implies (and (all-< (strip-cars acc) bound)
                (<= len bound))
           (all-< (strip-cars (array-to-alist-aux n len array-name array acc)) bound))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm all-<-of-strip-cars-of-array-to-alist
  (implies (<= len bound)
           (all-< (strip-cars (array-to-alist array-name array len)) bound))
  :hints (("Goal" :in-theory (enable array-to-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm nat-listp-of-strip-cars-of-cdr
   (implies (nat-listp (strip-cars x))
            (nat-listp (strip-cars (cdr x))))
   :hints (("Goal" :in-theory (enable array-to-alist)))))

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

;; Returns (mv probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes).
(defund initial-probable-facts-aux (node-to-value-alist ; grouped so that each group of nodes with the same val forms a contiguous block
                                   ;; accumulators:
                                   probably-equal-node-sets
                                   singleton-count
                                   probably-constant-node-alist
                                   never-used-nodes)
  (declare (xargs :guard (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                              (nat-listp (strip-cars node-to-value-alist))
                              (nat-list-listp probably-equal-node-sets)
                              (natp singleton-count)
                              (alistp probably-constant-node-alist)
                              (nat-listp never-used-nodes))
                  :guard-hints (("Goal" :in-theory (enable (:d strip-cars))))
                  :measure (len node-to-value-alist)))
  (if (atom node-to-value-alist)
      (mv probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)
    (b* ((entry (first node-to-value-alist))
         (nodenum (car entry))
         (value (cdr entry))
         ;; Skip this node and gather all immediately subsequent nodes with the same value.
         ((mv equiv-set node-to-value-alist)
          (leading-entries-with-value (rest node-to-value-alist) value nil))
         ((mv probably-equal-node-sets singleton-count)
          (if equiv-set ; there's at least one other node with the same value
              (mv (cons (cons nodenum equiv-set) probably-equal-node-sets) singleton-count)
            ;; only NODENUM has the value VALUE, so it is a singleton:
            (mv probably-equal-node-sets (+ 1 singleton-count))))
         ((mv probably-constant-node-alist never-used-nodes)
          (if (eq :unused value)
              ;; NODENUM is unused, as are all nodes in EQUIV-SET:
              (mv probably-constant-node-alist (cons nodenum (append equiv-set never-used-nodes)))
            ;; NODENUM and all nodes in EQUIV-SET candidates for always being equal to VALUE:
            (mv (acons-fast nodenum value (acons-all-to-val equiv-set value probably-constant-node-alist))
                never-used-nodes))))
      (initial-probable-facts-aux node-to-value-alist ; we've already moved past at least one entry
                                  probably-equal-node-sets
                                  singleton-count
                                  probably-constant-node-alist
                                  never-used-nodes))))


(local
 (defthm initial-probable-facts-aux-return-type
   (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                 (nat-listp (strip-cars node-to-value-alist))
                 (nat-list-listp probably-equal-node-sets)
                 (all-consp probably-equal-node-sets) ; no empty sets (in fact, there can't be singletons either)
                 (natp singleton-count)
                 (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (nat-listp never-used-nodes))
            (and (nat-list-listp (mv-nth 0 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)))
                 (all-consp (mv-nth 0 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)))
                 (natp (mv-nth 1 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)))
                 (alistp (mv-nth 2 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)))
                 (nat-listp (strip-cars (mv-nth 2 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes))))
                 (nat-listp (mv-nth 3 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)))))
   :hints (("Goal" :in-theory (enable initial-probable-facts-aux)))))

(local
  (defthm initial-probable-facts-aux-return-type-with-bound
    (implies (and (all-all-< probably-equal-node-sets bound)
                  (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                  (nat-listp (strip-cars node-to-value-alist))
                  (all-< (strip-cars node-to-value-alist) bound)
                  (nat-list-listp probably-equal-node-sets)
                  (natp singleton-count)
                  (alistp probably-constant-node-alist)
                  (nat-listp never-used-nodes)
                  (all-< (strip-cars probably-constant-node-alist)
                         bound)
                  (all-< never-used-nodes bound))
             (and (all-all-< (mv-nth 0 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes))
                             bound)
                  (all-< (strip-cars (mv-nth 2 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes)))
                         bound)
                  (all-< (mv-nth 3 (initial-probable-facts-aux node-to-value-alist probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes))
                         bound)))
    :hints (("Goal" :in-theory (enable initial-probable-facts-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assumes the TEST-CASE-ARRAY gives values for the current test case to all nodes below DAG-LEN.
;; Returns (mv probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes).
(defund initial-probable-facts (dag-len test-case-array-name test-case-array)
  (declare (xargs :guard (and (array1p test-case-array-name test-case-array)
                              (natp dag-len)
                              (<= dag-len (alen1 test-case-array-name test-case-array)))))
  (let* ((node-to-value-alist (array-to-alist test-case-array-name test-case-array dag-len))
         ;; We sort here just to group entries with the same value together:
         (sorted-node-to-value-alist (merge-sort-lexorder-of-cdrs node-to-value-alist)))
    (initial-probable-facts-aux sorted-node-to-value-alist nil 0 nil nil)))

(local
 (defthm all-all-<-of-mv-nth-0-of-initial-probable-facts
   (implies (and (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 (<= dag-len bound))
            (all-all-< (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array)) bound))
   :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm all-consp-of-mv-nth-0-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (all-consp (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-list-listp (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm natp-of-mv-nth-1-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (natp (mv-nth 1 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (e/d (initial-probable-facts) (natp))))))

(local
 (defthm alistp-of-mv-nth-2-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (alistp (mv-nth 2 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (e/d (initial-probable-facts) ())))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-2-of-initial-probable-facts
   (implies (and (<= dag-len bound)
                 (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 )
            (all-< (strip-cars (mv-nth 2 (initial-probable-facts dag-len test-case-array-name test-case-array)))
                   bound))
   :hints (("Goal" :in-theory (e/d (initial-probable-facts) ())))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-2-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-listp (strip-cars (mv-nth 2 (initial-probable-facts dag-len test-case-array-name test-case-array)))))
  :hints (("Goal" :in-theory (e/d (initial-probable-facts) ())))))

(local
 (defthm nat-listp-of-mv-nth-3-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-listp (mv-nth 3 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (e/d (initial-probable-facts) ())))))

(local
 (defthm all-<-of-mv-nth-3-of-initial-probable-facts
   (implies (and (<= dag-len bound)
                 (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 )
            (all-< (mv-nth 3 (initial-probable-facts dag-len test-case-array-name test-case-array)) bound))
   :hints (("Goal" :in-theory (e/d (initial-probable-facts) ())))))

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

(defun find-val-other-than (val nodenums test-case-array test-case-array-name)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (array1p test-case-array-name test-case-array)
                              (all-< nodenums (alen1 test-case-array-name test-case-array)))))
  (if (endp nodenums)
      nil ;failed to find such a val
    (let* ((nodenum (first nodenums))
           (val2 (aref1 test-case-array-name test-case-array nodenum)))
      (if (equal val val2)
          ;;keep looking:
          (find-val-other-than val (cdr nodenums) test-case-array test-case-array-name)
        ;;we found a difference:
        t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns an alist pairing values with nodenum lists
;the alist may include shadowed pairs
;fixme think about :unused nodes
(defund test-case-alist-for-set (set test-case-array-name test-case-array acc)
  (declare (xargs :guard (and (nat-listp set)
                              (array1p test-case-array-name test-case-array)
                              (all-< set (alen1 test-case-array-name test-case-array))
                              (alistp acc))))
  (if (endp set)
      acc
    (let* ((nodenum (first set))
           (value (aref1 test-case-array-name test-case-array nodenum))
           (nodes-for-value (lookup-equal value acc)))
      (test-case-alist-for-set (cdr set) test-case-array-name test-case-array
                               (acons-fast value (cons nodenum nodes-for-value) acc)))))

(local
 (defthm alistp-of-test-case-alist-for-set
   (implies (alistp acc)
            (alistp (test-case-alist-for-set set test-case-array-name test-case-array acc)))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set)))))

(local
 (defthm all-consp-of-strip-cdrs-of-test-case-alist-for-set
   (implies (all-consp (strip-cdrs acc))
            (all-consp (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc))))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set)))))

(local
 (defthm all-all-<-of-strip-cdrs-of-test-case-alist-for-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (alistp acc)
                 (all-all-< (strip-cdrs acc) bound)
                 (<= (alen1 test-case-array-name test-case-array) bound))
            (all-all-< (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc)) bound))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set all-all-<)))))

(local
 (defthm nat-list-listp-of-strip-cdrs-of-test-case-alist-for-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (alistp acc)
                 (NAT-LIST-LISTP (STRIP-CDRS ACC)))
            (nat-list-listp (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc))))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set nat-list-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv non-singletons singleton-count).
(defund drop-and-count-singletons (lst non-singletons-acc count-acc)
  (declare (xargs :guard (and (integerp count-acc)
                              (true-listp lst))))
  (if (endp lst)
      (mv non-singletons-acc count-acc)
    (let* ((item (car lst)))
      (if (and (consp item) ; drop if all are known to be non empty lists?
               (not (consp (cdr item))))
          ;; it's a singleton, so drop it and count it:
          (drop-and-count-singletons (cdr lst) non-singletons-acc (+ 1 count-acc))
        ;; it's not a singleton, so keep it:
        (drop-and-count-singletons (cdr lst) (cons item non-singletons-acc) count-acc)))))

(local
 (defthm true-listp-of-mv-nth-0-of-drop-and-count-singletons
   (implies (true-listp acc)
            (true-listp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-drop-and-count-singletons
   (implies (and (nat-list-listp acc)
                 (nat-list-listp lst))
            (nat-list-listp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons
                                      nat-list-listp)))))

(local
 (defthm all-consp-of-mv-nth-0-of-drop-and-count-singletons
   (implies (and (all-consp acc)
                 (all-consp lst)
                 )
            (all-consp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons
                                      nat-list-listp)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-drop-and-count-singletons
   (implies (and (all-all-< acc bound)
                 (all-all-< lst bound)
                 )
            (all-all-< (mv-nth 0 (drop-and-count-singletons lst acc count-acc))
                       bound))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons
                                      nat-list-listp
                                      all-all-<)))))

(local
 (defthm natp-mv-nth-1-of-drop-and-count-singletons
   (implies (natp count-acc)
            (natp (mv-nth 1 (drop-and-count-singletons lst acc count-acc))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable drop-and-count-singletons)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;ignores later pairs that bind already-bound keys
(defund strip-cdrs-unique (lst keys-seen acc)
  (declare (xargs :guard (and (alistp lst)
                              (true-listp keys-seen))))
  (if (endp lst)
      acc ;we don't bother to reverse this
    (let* ((entry (car lst))
           (key (car entry)))
      (if (member-equal key keys-seen)
          (strip-cdrs-unique (cdr lst) keys-seen acc)
        (strip-cdrs-unique (cdr lst) (cons key keys-seen) (cons (cdr entry) acc))))))

(local
 (defthm true-listp-of-strip-cdrs-unique
   (implies (true-listp acc)
            (true-listp (strip-cdrs-unique lst keys-seen acc)))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique)))))

(local
 (defthm nat-list-listp-of-strip-cdrs-unique
   (implies (and (nat-list-listp acc)
                 (nat-list-listp (strip-cdrs lst)))
            (nat-list-listp (strip-cdrs-unique lst keys-seen acc)))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp)))))

(local
 (defthm all-consp-of-strip-cdrs-unique
   (implies (and (all-consp acc)
                 (all-consp (strip-cdrs lst)))
            (all-consp (strip-cdrs-unique lst keys-seen acc)))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp)))))

(local
 (defthm all-all-<-of-strip-cdrs-unique
   (implies (and (all-all-< acc bound)
                 (all-all-< (strip-cdrs lst) bound))
            (all-all-< (strip-cdrs-unique lst keys-seen acc) bound))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp all-all-<)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;we first make an alist whose keys are data values (often 0 or 1?) and whose vals are sets of nodenums
;returns (mv new-sets new-singleton-count)
(defund split-set (set test-case-array test-case-array-name)
  (declare (xargs :guard (and (nat-listp set)
                              (array1p test-case-array-name test-case-array)
                              (all-< set (alen1 test-case-array-name test-case-array)))))
  (let* ((alist (test-case-alist-for-set set test-case-array-name test-case-array nil)) ;this could be slow?  better to pair nodenums with vals and merge-sort the pairs by value?
         (new-node-sets (strip-cdrs-unique alist nil nil)) ;don't cons this up?
         )
    ;;fixme combine this with the work above:
    (drop-and-count-singletons new-node-sets nil 0)))

(local
 (defthm true-listp-of-mv-nth-0-of-split-set
   (true-listp (mv-nth 0 (split-set set test-case-array test-case-array-name)))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-split-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array)))
            (nat-list-listp (mv-nth 0 (split-set set test-case-array test-case-array-name))))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm all-consp-of-mv-nth-0-of-split-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array)))
            (all-consp (mv-nth 0 (split-set set test-case-array test-case-array-name))))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-split-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (<= (alen1 test-case-array-name test-case-array) bound))
            (all-all-< (mv-nth 0 (split-set set test-case-array test-case-array-name))
                       bound))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm natp-of-mv-nth-1-of-split-set
   (natp (mv-nth 1 (split-set set test-case-array test-case-array-name)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-set)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;takes a set and adds zero or more sets to acc (also returns a new singleton count)
;returns (mv acc new-singleton-count change-flg)
;set should have at least two elements
;should not return singletons or empty sets
;most of the time, this won't be able to distinguish any nodes and so will return (list set) - we try to make that case fast (don't recons the whole set)...
;inline this?
(defund try-to-split-set (set test-case-array-name test-case-array print acc)
  (declare (xargs :guard (and (nat-listp set)
                              (consp set)
                              (array1p test-case-array-name test-case-array)
                              ;; print
                              (all-< set (alen1 test-case-array-name test-case-array))
                              (true-listp acc))))
  (let* ((first-nodenum (first set))
         (first-val (aref1 test-case-array-name test-case-array first-nodenum))
         (need-to-splitp (find-val-other-than first-val (rest set) test-case-array test-case-array-name)))
    (if (not need-to-splitp)
        ;;in this case we don't recons the whole set
        (mv (cons set acc) 0 nil)
      (prog2$ (and print (cw "~% (Splitting a set of ~x0 nodes.)" (len set)))
              (mv-let (new-sets new-singleton-count)
                      (split-set set test-case-array test-case-array-name) ;todo: pass acc into this?
                      (mv (append new-sets acc)
                          new-singleton-count t))))))

(local
 (defthm true-listp-of-mv-nth-0-of-try-to-split-set
   (implies (true-listp acc)
            (true-listp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (consp set)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc))
            (nat-list-listp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm all-consp-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (consp set)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc)
                 (all-consp acc))
            (all-consp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (all-< set bound)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc)
                 (all-all-< acc bound)
                 (<= (alen1 test-case-array-name test-case-array) bound)
                 )
            (all-all-< (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))
                       bound))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm natp-of-mv-nth-1-of-try-to-split-set
   (natp (mv-nth 1 (try-to-split-set set test-case-array-name test-case-array print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm booleanp-of-mv-nth-2-of-try-to-split-set
   (booleanp (mv-nth 2 (try-to-split-set set test-case-array-name test-case-array print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to split the sets using test-case-array.
;; Returns (mv new-sets new-singleton-count changep),
;sets are moved from SETS to ACC.  as they are moved they are split if indicated by this test case.
;sets are lists of nodenums.  each set has length at least 2 (singleton sets are dropped).
(defund update-probably-equal-node-sets (sets test-case-array acc singleton-count-acc print test-case-array-name changep)
  (declare (xargs :guard (and (nat-list-listp sets)
                              (all-consp sets)
                              (array1p test-case-array-name test-case-array)
                              (true-listp acc)
                              (natp singleton-count-acc)
                              ;; print
                              (all-all-< sets (alen1 test-case-array-name test-case-array))
                              (booleanp changep))
                  :guard-hints (("Goal" :in-theory (enable all-all-<)))))
  (if (endp sets)
      (mv acc singleton-count-acc changep)
    (let* ((set (first sets)))
      (mv-let (acc ;has the new sets appended onto it
               new-singleton-count change-flg-for-this-set)
              (try-to-split-set set test-case-array-name test-case-array print acc)
              (update-probably-equal-node-sets (rest sets)
                                            test-case-array
                                            acc
                                            (+ singleton-count-acc new-singleton-count)
                                            print
                                            test-case-array-name
                                            (or changep change-flg-for-this-set))))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-update-probably-equal-node-sets
   (implies (and (nat-list-listp sets)
                 (nat-list-listp acc)
          ;                (all-consp acc)
                 (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (nat-list-listp (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

(local
 (defthm all-consp-of-mv-nth-0-of-update-probably-equal-node-sets
   (implies (and (nat-list-listp sets)
                 (nat-list-listp acc)
                 (all-consp acc)
                 (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (all-consp (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-update-probably-equal-node-sets
   (implies (and (<= (alen1 test-case-array-name test-case-array) dag-len)
                 (nat-list-listp sets)
                 (nat-list-listp acc)
                 (all-consp acc)
                 (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 (ALL-ALL-< ACC DAG-LEN)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (all-all-< (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))
                       dag-len))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

(local
 (defthm natp-of-mv-nth-1-of-update-probably-equal-node-sets
   (implies (natp singleton-count-acc)
            (natp (mv-nth 1 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets)))))

(local
 (defthm booleanp-of-mv-nth-2-of-update-probably-equal-node-sets
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets)))))

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

;Handles nodes that are used on this test case but have not been used on a previous test case.
;Such nodes are moved from the never-used-nodes list to the probably-constant-node-alist, where they are paired with their value on this test case.
;Returns (mv never-used-nodes probably-constant-node-alist changep) where changep remains true if it was initially true.
(defund handle-newly-used-nodes (never-used-nodes ;these are moved to acc or get entries in the alist
                                 probably-constant-node-alist ;;pairs nodenums with probable constants
                                 test-case-array-name test-case-array
                                 acc
                                 changep)
  (declare (xargs :guard (and (nat-listp never-used-nodes)
                              (alistp probably-constant-node-alist)
                              (array1p test-case-array-name test-case-array)
                              (all-< never-used-nodes (alen1 test-case-array-name test-case-array))
                              ;; acc
                              (booleanp changep))))
  (if (endp never-used-nodes)
      (mv acc probably-constant-node-alist changep)
    (let* ((nodenum (first never-used-nodes))
           (value (aref1 test-case-array-name test-case-array nodenum)))
      (if (eq :unused value)
          ;; the node is still unused:
          (handle-newly-used-nodes (rest never-used-nodes)
                                   probably-constant-node-alist
                                   test-case-array-name test-case-array
                                   (cons nodenum acc)
                                   changep)
        ;;the node is used for the first time on this test case:
        (handle-newly-used-nodes (rest never-used-nodes)
                                 (acons-fast nodenum value probably-constant-node-alist)
                                 test-case-array-name test-case-array
                                 acc
                                 t)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp acc))
            (nat-listp (mv-nth 0 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm all-<-of-mv-nth-0-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist)
                 (array1p test-case-array-name test-case-array)
                 (all-< never-used-nodes (alen1 test-case-array-name test-case-array))
                 (all-< never-used-nodes dag-len)
                 (all-< acc dag-len)
                 (booleanp changep))
            (all-< (mv-nth 0 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))
                   dag-len))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm alistp-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (alistp probably-constant-node-alist)
            (alistp (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp (strip-cars probably-constant-node-alist)))
            (nat-listp (strip-cars (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep)))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (and (all-< never-used-nodes bound)
                 (all-< (strip-cars probably-constant-node-alist) bound))
            (all-< (strip-cars (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm booleanp-of-mv-nth-2-of-handle-newly-used-nodes
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this function drops any pairs which are invalidated by the current test case
;this rebuilds the whole alist - hope that is okay...
;returns (mv probably-constant-node-alist changep)
;fixme might be faster to process more than 1 test case at a time
;every node in probably-constant-node-alist has been used on at least one test case
(defund update-probably-constant-alist (probably-constant-node-alist ;;pairs nodenums with probable constants
                                     test-case-array-name test-case-array
                                     acc ;pairs are moved from probably-constant-node-alist to this
                                     changep)
  (declare (xargs :guard (and (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (array1p test-case-array-name test-case-array)
                              (all-< (strip-cars probably-constant-node-alist)
                                     (alen1 test-case-array-name test-case-array))
                              ;; acc
                              (booleanp changep))))
  (if (endp probably-constant-node-alist)
      (mv acc changep)
    (let* ((pair (first probably-constant-node-alist))
           (nodenum (car pair))
           (probable-value (cdr pair))
           (value-for-this-test-case (aref1 test-case-array-name test-case-array nodenum)))
      (if (or (eq :unused value-for-this-test-case)
              (equal probable-value value-for-this-test-case))
          ;; this test case doesn't invalidate the pair:
          (update-probably-constant-alist (rest probably-constant-node-alist) test-case-array-name test-case-array
                                       (cons pair acc) changep)
        ;; the node is used and the value is different from the value in the alist, so drop the pair:
        (update-probably-constant-alist (rest probably-constant-node-alist) test-case-array-name test-case-array
                                     acc t)))))

(local
 (defthm alistp-of-mv-nth-0-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (alistp acc)
                 (booleanp changep))
            (alistp (mv-nth 0 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

(local
 (defthm booleanp-of-mv-nth-1-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (alistp acc)
                 (booleanp changep))
            (booleanp (mv-nth 1 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-0-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (booleanp changep))
            (nat-listp (strip-cars (mv-nth 0 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep)))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-0-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (ALL-< (STRIP-CARS ACC) BOUND)
                 (booleanp changep)
                 (<= (alen1 test-case-array-name test-case-array) bound)
                 )
            (all-< (strip-cars (mv-nth 0 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; run test cases and use them to split probably-equal-node-sets and eliminate probable constants
;; returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist), where test-case-array-alist is valid iff keep-test-casesp is non-nil
;ffixme think about what to do with nodes that are unreachable (don't influence the top node, because of ifs) on a single test case, or on all test cases.  maybe i now handle that?
;now the tests come in randomized?
(defund update-probable-facts-with-test-cases (test-cases
                                               singleton-count
                                               dag-array-name dag-array dag-len
                                               probably-equal-node-sets
                                               never-used-nodes
                                               probably-constant-node-alist
                                               interpreted-function-alist print
                                               test-case-array-name-base
                                               keep-test-casesp
                                               test-case-array-alist
                                               test-case-number
                                               debug-nodes
                                               num-of-last-interesting-test-case)
  (declare (xargs :guard (and (test-casesp test-cases)
                              (natp singleton-count)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (nat-list-listp probably-equal-node-sets)
                              (all-consp probably-equal-node-sets)
                              (all-all-< probably-equal-node-sets dag-len)
                              (nat-listp never-used-nodes)
                              (all-< never-used-nodes dag-len)
                              (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (all-< (strip-cars probably-constant-node-alist) dag-len)
                              (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                              (symbolp test-case-array-name-base)
                              (booleanp keep-test-casesp)
                              (alistp test-case-array-alist)
                              (natp test-case-number)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes dag-len)
                              (or (null num-of-last-interesting-test-case)
                                  (natp num-of-last-interesting-test-case)))
                  :guard-hints (("Goal" :in-theory (disable natp strip-cars)))))
  (if (or (endp test-cases)
          ;;stop if we've done at least 100 test cases and nothing has happened in the last 90% of them:
          ;;fixme could allow the user to change the 10 and the 100 here:
          (if (and t ;abandon-testing-when-boringp ;(or t abandon-testing-when-boringp)
                   num-of-last-interesting-test-case
                   (<= 100 test-case-number)
                   (<= (* 10 num-of-last-interesting-test-case) test-case-number))
              (prog2$ (cw "(Abandoning testing because nothing interesting is happening.)")
                      t)
            nil))
      (mv t ; all tests passed
          probably-equal-node-sets never-used-nodes probably-constant-node-alist
          (reverse test-case-array-alist) ;new; keeps this in sync with the test cases (or do non-interesting ones get dropped?)
          )
    (b* ((- ;;TODO: Only print when things change?:
          (cw "(Test ~x0 (~x1 total sets, ~x2 singletons, ~x3 constants)"
              test-case-number
              (+ singleton-count (len probably-equal-node-sets)) ;slow? could keep a count?
              singleton-count
              (len probably-constant-node-alist) ;slow?
              ))
         (test-case (first test-cases))
         (test-case-array-name (if keep-test-casesp
                                   (pack$ test-case-array-name-base '- (nat-to-string test-case-number))
                                 ;;if we are not keeping test cases (e.g., because they'd take too much memory), reuse the same array:
                                 test-case-array-name-base))
         ;; Evaluate the test case and ensure the top node is true:
         (test-case-array
          (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist
                                        test-case-array-name
                                        debug-nodes))
         ((when (not test-case-array)) ; some test failed! (rare)
          (mv nil probably-equal-node-sets never-used-nodes probably-constant-node-alist nil))
         (changep nil) ; track whether this test case was interesting
         ;; Update the probably-equal-node-sets:
         ((mv new-sets new-singleton-count changep)
          (update-probably-equal-node-sets probably-equal-node-sets test-case-array nil 0 print test-case-array-name changep))
         ;; Maybe invalidate some probable constants (done before handle-newly-used-nodes, which may add new probable constants):
         ((mv probably-constant-node-alist changep)
          (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array nil changep))
         ;; Handle nodes that are used for the first time on this test case (they become probable constants):
         ((mv never-used-nodes probably-constant-node-alist changep)
          (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array nil changep))
         (- (if (and (or (eq print :verbose)
                         (eq print :verbose!))
                     changep) ; todo: use this value to decide whether to keep the test case? maybe keep the first few boring ones so we have enough..
                (cw "~%interesting test case ~x0.)~%" test-case)
              (cw ")~%"))))
      (update-probable-facts-with-test-cases (rest test-cases)
                                             (+ singleton-count new-singleton-count)
                                             dag-array-name dag-array dag-len
                                             new-sets
                                             never-used-nodes
                                             probably-constant-node-alist
                                             interpreted-function-alist print test-case-array-name-base keep-test-casesp
                                             (if keep-test-casesp
                                                 (acons-fast test-case-array-name
                                                             test-case-array
                                                             test-case-array-alist)
                                               nil)
                                             (+ 1 test-case-number)
                                             debug-nodes
                                             (if changep
                                                 test-case-number
                                               num-of-last-interesting-test-case)))))

(defthm nat-list-listp-of-mv-nth-1-of-update-probable-facts-with-test-cases
  (implies (and (test-casesp test-cases)
                (natp singleton-count)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< 0 dag-len)
                (nat-list-listp probably-equal-node-sets)
                (all-consp probably-equal-node-sets)
                (all-all-< probably-equal-node-sets dag-len)
                (nat-listp never-used-nodes)
                (all-< never-used-nodes dag-len)
                (alistp probably-constant-node-alist)
                (nat-listp (strip-cars probably-constant-node-alist))
                (all-< (strip-cars probably-constant-node-alist) dag-len)
                (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                (symbolp test-case-array-name-base)
                (booleanp keep-test-casesp)
                (alistp test-case-array-alist)
                (natp test-case-number)
                (nat-listp debug-nodes)
                (all-< debug-nodes dag-len)
                (or (null num-of-last-interesting-test-case)
                    (natp num-of-last-interesting-test-case)))
           (nat-list-listp (mv-nth 1 (update-probable-facts-with-test-cases test-cases
                                                                            singleton-count
                                                                            dag-array-name dag-array dag-len
                                                                            probably-equal-node-sets
                                                                            never-used-nodes
                                                                            probably-constant-node-alist
                                                                            interpreted-function-alist print
                                                                            test-case-array-name-base
                                                                            keep-test-casesp
                                                                            test-case-array-alist
                                                                            test-case-number
                                                                            debug-nodes
                                                                            num-of-last-interesting-test-case))))
  :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases))))

(defthm nat-listp-of-mv-nth-2-of-update-probable-facts-with-test-cases
  (implies (nat-listp never-used-nodes)
           (nat-listp (mv-nth 2 (update-probable-facts-with-test-cases test-cases
                                                                       singleton-count
                                                                       dag-array-name dag-array dag-len
                                                                       probably-equal-node-sets
                                                                       never-used-nodes
                                                                       probably-constant-node-alist
                                                                       interpreted-function-alist print
                                                                       test-case-array-name-base
                                                                       keep-test-casesp
                                                                       test-case-array-alist
                                                                       test-case-number
                                                                       debug-nodes
                                                                       num-of-last-interesting-test-case))))
  :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases))))

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

;; Repeatedly generates a test case and then use it to split possibly-equal node sets and eliminate possibly-constant nodes.
;; Returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist),
;; where probably-equal-node-sets includes nodes believed to be constant and probably-constant-node-alist pairs nodes with the constants they seem to be equal to
;; and test-case-array-alist is valid iff keep-test-casesp is non-nil and pairs array names with arrays that give values to all the nodes.
;todo: should this return the used test cases (I guess they can be extracted from the test-case-array-alist)?
(defund find-probable-facts (miter-array-name
                             miter-array
                             miter-len
                             miter-depth
                             test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
                             interpreted-function-alist
                             print
                             keep-test-casesp
                             debug-nodes)
  (declare (xargs :guard (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                              (< 0 miter-len)
                              (natp miter-depth)
                              (test-casesp test-cases)
                              (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                              (booleanp keep-test-casesp)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes miter-len))
                  :guard-hints (("Goal" :in-theory (disable natp)))))
  (b* ((test-cases test-cases ;(firstn 1024 test-cases) ;Thu Feb 17 20:25:10 2011
                   )
       (- (cw "(Evaluating test cases (keep-test-casesp is ~x0):~%" keep-test-casesp))
       ;; use the first test case to make initial-probably-equal-node-sets (I think this is faster than starting with one huge set and then splitting it):
       (- (cw "(Test 0 (initial)"))
       (test-case-array-name-base (pack$ 'test-case-array-depth- miter-depth '-)) ;using the depth is new
       (first-test-case-array-name (pack$ test-case-array-name-base 0))
       (test-case-array
        (evaluate-and-check-test-case (first test-cases)
                                      miter-array-name
                                      miter-array
                                      miter-len
                                      interpreted-function-alist
                                      first-test-case-array-name
                                      debug-nodes))
       ((when (not test-case-array)) ; actually, a hard error will have already been thrown
        (mv nil                      ; all-passedp
            nil nil nil nil))
       ((mv initial-probably-equal-node-sets
            initial-singleton-count
            initial-probably-constant-node-alist ;pairs nodenums used on the first test case with their values
            initial-never-used-nodes)
        (initial-probable-facts miter-len first-test-case-array-name test-case-array))
       ;;((array-to-alist first-test-case-array-name test-case-array miter-len)) ;slow?
       ;;save the first test case in the test-case-array-alist:
       (test-case-array-alist (if keep-test-casesp
                                  (acons-fast first-test-case-array-name test-case-array nil)
                                nil))
       (- (cw ")~%"))
       ;;use additional test cases to split the sets and update the probable constant facts:
       ((mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist)
        (update-probable-facts-with-test-cases (rest test-cases)
                                               initial-singleton-count
                                               miter-array-name
                                               miter-array
                                               miter-len
                                               initial-probably-equal-node-sets
                                               initial-never-used-nodes
                                               initial-probably-constant-node-alist
                                               interpreted-function-alist
                                               print
                                               test-case-array-name-base
                                               keep-test-casesp ;just check whether test-case-array-alist is nil?
                                               test-case-array-alist
                                               1 ;test case number
                                               debug-nodes
                                               nil ;;number of last interesting test case
                                               ))
       (probably-equal-node-sets (remove-set-of-unused-nodes probably-equal-node-sets never-used-nodes nil)) ;TODO: could try to prove that these are really unused (could give interesting counterexamples)
       (- (cw ")~%")))
    (mv all-passedp
        probably-equal-node-sets
        never-used-nodes
        probably-constant-node-alist
        test-case-array-alist)))

(defthm nat-list-listp-of-mv-nth-1-of-find-probable-facts
  (implies (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                (< 0 miter-len)
                (natp miter-depth)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                (booleanp keep-test-casesp)
                (nat-listp debug-nodes)
                (all-< debug-nodes miter-len))
           (nat-list-listp (mv-nth 1 (find-probable-facts miter-array-name miter-array miter-len
                                                          miter-depth
                                                          test-cases
                                                          interpreted-function-alist print keep-test-casesp
                                                          debug-nodes))))
  :hints (("Goal" :in-theory (enable find-probable-facts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist).
;; Only used to compute the facts for printing, since usually we have a dag-array rather than a dag.
(defund find-probable-facts-for-dag (dag
                                     test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
                                     interpreted-function-alist
                                     ;print
                                     keep-test-casesp
                                     ;debug-nodes
                                     )
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) 2147483646)
                              (test-casesp test-cases)
                              (interpreted-function-alistp interpreted-function-alist)
                              (booleanp keep-test-casesp))))
  (let* ((miter-array-name 'probable-facts-array)
         (miter-array (make-into-array miter-array-name dag))
         (miter-len (len dag)))
    (find-probable-facts miter-array-name
                         miter-array
                         miter-len
                         0 ; miter-depth
                         test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
                         interpreted-function-alist
                         nil ; print
                         keep-test-casesp
                         nil ; debug-nodes
                         )))

(defthm nat-list-listp-of-mv-nth-1-of-find-probable-facts-for-dag
  (implies (and (pseudo-dagp dag)
                (<= (len dag) 2147483646)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
                (booleanp keep-test-casesp))
           (nat-list-listp (mv-nth 1 (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp))))
  :hints (("Goal" :in-theory (enable find-probable-facts-for-dag))))

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
(defthmd all-nat-listp-when-nat-list-listp
  (implies (nat-list-listp x)
           (all-nat-listp x))
  :hints (("Goal" :in-theory (enable nat-list-listp all-nat-listp))))

(defund print-probable-facts-for-test-cases (dag
                                             test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
                                             interpreted-function-alist
                                             keep-test-casesp)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) 2147483646)
                              (test-casesp test-cases)
                              (interpreted-function-alistp interpreted-function-alist)
                              (booleanp keep-test-casesp))
                  :guard-hints (("Goal" :in-theory (enable true-listp-when-nat-list-listp
                                                           all-nat-listp-when-nat-list-listp)))))
  (mv-let (all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist)
    (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp)
    ;(declare (ignore test-case-array-alist))
    (progn$ (cw "All passed: ~x0.~%" all-passedp)
            (cw "~x0 probably-equal-node-sets: ~X12.~%" (len probably-equal-node-sets)
                (merge-sort-<-of-mins probably-equal-node-sets)
                nil)
            (cw "~x0 never-used-nodes: ~X12.~%" (len never-used-nodes) never-used-nodes nil)
            (cw "probably-constant-node-alist: ~x0.~%" probably-constant-node-alist)
            ;; Do we always want to print this one?:
            (cw "test-case-array-alist: ~x0.~%" test-case-array-alist))))

;; Just prints the probable facts for a DAG (e.g., for examination to find new rewrite rules).
;; Returns rand.
(defund print-probable-facts-for-dag (dag test-case-count test-case-type-alist interpreted-fns keep-test-casesp wrld rand)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) 2147483646)
                              (natp test-case-count)
                              (test-case-type-alistp test-case-type-alist)
                              (symbol-listp interpreted-fns)
                              (booleanp keep-test-casesp)
                              (plist-worldp wrld))
                  :stobjs rand))
  (b* (((mv erp test-cases rand)
        (make-test-cases test-case-count test-case-type-alist nil rand))
       ((when erp) (cw "Error making test cases.") rand)
       (- (print-probable-facts-for-test-cases dag test-cases (make-interpreted-function-alist interpreted-fns wrld) keep-test-casesp)))
    rand))
