; Alternate tools to rebuild nodes with substitutions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rebuild-nodes") ;todo: reduce
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "meta/meta-plus-lessp" :dir :system))
(local (include-book "merge-sort-less-than-rules"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))

;; Utilities to rebuild nodes (e.g., for substitution) that starts at the
;; target node and moves upward, handling its parents, their parents, etc.

(local (in-theory (disable no-duplicatesp-equal)))

;move
(defthm member-equal-of-remove-duplicates-equal-iff
  (iff (member-equal a (remove-duplicates-equal x))
       (member-equal a x)))

;move
(defthm NO-DUPLICATESP-EQUAL-of-REMOVE-DUPLICATES-EQUAL
  (NO-DUPLICATESP-EQUAL (REMOVE-DUPLICATES-EQUAL x))
  :hints (("Goal" :in-theory (enable NO-DUPLICATESP-EQUAL))))

(defthm nat-listp-of-remove-duplicates-equal
  (implies (nat-listp x)
           (nat-listp (remove-duplicates-equal x))))

(local
 (defthm acl2-numberp-when-natp
   (implies (natp x)
            (acl2-numberp x))))

(defthm car-of-merge-<
  (equal (car (merge-< l1 l2 acc))
         (if (consp acc)
             (nth (+ -1 (len acc)) acc)
           (if (not (consp l1))
               (car l2)
             (if (not (consp l2))
                 (car l1)
               (if (< (car l1) (car l2))
                   (car l1)
                 (car l2))))))
  :hints (("Goal" :in-theory (enable merge-<))))


;; todo: this must exist somewhere?
;; Leaves one member of each run of consecutive duplicates
(defund remove-duplicates-from-sorted-list (list acc)
  (declare (xargs :guard (and (all-natp list)
                              (true-listp list)
                              (all-natp acc)
                              (true-listp acc))))
  (if (endp list)
      (reverse-list acc)
    (let ((first (first list)))
      (if (endp (rest list))
          (reverse-list (cons first acc))
        (if (equal first (second list))
            ;; Drop the first element:
            (remove-duplicates-from-sorted-list (rest list) acc)
          (remove-duplicates-from-sorted-list (rest list) (cons first acc)))))))

(defthm car-of-remove-duplicates-from-sorted-list
  (equal (car (remove-duplicates-from-sorted-list list acc))
         (if (consp acc)
             (nth (+ -1 (len acc)) acc)
           (car list)))
  :hints (("Goal" :in-theory (enable remove-duplicates-from-sorted-list))))

(defthm consp-of-remove-duplicates-from-sorted-list
  (equal (consp (remove-duplicates-from-sorted-list list acc))
         (or (consp list)
             (consp acc)))
  :hints (("Goal" :in-theory (enable remove-duplicates-from-sorted-list))))

(defthm all-<-of-remove-duplicates-from-sorted-list
  (equal (all-< (remove-duplicates-from-sorted-list list acc) bound)
         (and (all-< list bound)
              (all-< acc bound)))
  :hints (("Goal" :in-theory (enable remove-duplicates-from-sorted-list))))

(defthm all-<=-of-car-when-all-<=-of-all
  (implies (and (all-<=-all acc list)
                (consp list))
           (all-<= acc (car list))))

(defthmd not-<-of-car-when-<=-all
  (implies (and (<=-all x y)
                (consp y))
           (not (< (car y) x)))
  :hints (("Goal" :in-theory (enable <=-all))))

(defthm sortedp-<=-of-remove-duplicates-from-sorted-list
  (equal (sortedp-<= (remove-duplicates-from-sorted-list list acc))
         (and (sortedp-<= list)
              (sortedp-<= (reverse-list acc))
              (all-<=-all acc list)))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable sortedp-<=
                              remove-duplicates-from-sorted-list
                              not-<-of-car-when-<=-all
                              <=-of-first-and-second-when-sortedp))))

(defthm sortedp-<=-of-singleton
  (sortedp-<= (list x))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthmd <=-of-cadr-and-car-when-sortedp-<=
  (implies (and (sortedp-<= list)
                (consp (cdr list))
                (all-natp list)
                )
           (equal (< (CAR LIST) (CADR LIST))
                  (not (equal (CADR LIST) (CAR LIST)))))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthm no-duplicatesp-equal-of-remove-duplicates-from-sorted-list
  (implies (and (sortedp-<= list)
                (sortedp-<= (reverse-list acc))
                ;;(not (equal (first acc) (first list)))
                ;;(no-duplicatesp-equal list)
                (no-duplicatesp-equal acc)
                ;;(all-<=-all acc list)
                (or (not (consp acc))
                    (< (first acc) (first list)))
                (all-natp list))
           (no-duplicatesp-equal (remove-duplicates-from-sorted-list list acc)))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable no-duplicatesp-equal
                              remove-duplicates-from-sorted-list
                              not-<-of-car-when-<=-all
                              <=-of-first-and-second-when-sortedp
                              <=-of-cadr-and-car-when-sortedp-<=))))

(defthm nat-listp-of-remove-duplicates-from-sorted-list
  (equal (nat-listp (remove-duplicates-from-sorted-list list acc))
         (and (nat-listp (true-list-fix list))
              (nat-listp (reverse-list acc))))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable nat-listp
                              remove-duplicates-from-sorted-list
                              not-<-of-car-when-<=-all
                              <=-of-first-and-second-when-sortedp))))

(defthm all-<-of-merge-<
  (equal (all-< (merge-< l1 l2 acc) bound)
         (and (all-< l1 bound)
              (all-< l2 bound)
              (all-< acc bound)))
  :hints (("Goal" :in-theory (enable merge-<))))

;; (defthm all->-of-merge-<
;;   (equal (all-> (merge-< l1 l2 acc) bound)
;;          (and (all-> l1 bound)
;;               (all-> l2 bound)
;;               (all-> acc bound)))
;;   :hints (("Goal" :in-theory (enable merge-< ALL-> REVAPPEND-LEMMA))))

;; (defthm all->-of-merge-sort-<
;;   (equal (all-> (merge-sort-< l1) bound)
;;          (all-> l1 bound))
;;   :hints (("Goal" :in-theory (enable merge-sort-<))))


;; (remove-duplicates-from-sorted-list '(0 1 1 2 3 3 3 4 4)  nil)

(defthmd <-of-first-and-second-when-sortedp-and-no-duplicatesp-equal
  (implies (and (all-natp x)
                (sortedp-<= x)
                (consp (cdr x))
                (no-duplicatesp-equal x))
           (< (first x) (second x)))
  :hints (("Goal" :in-theory (enable sortedp-<= NO-DUPLICATESP-EQUAL))))

(defthmd natp-of-cadr-when-all-natp
  (implies (all-natp x)
           (equal (NATP (CADR x))
                  (consp (cdr x)))))

(defthm all-<-forward-to-<-of-car
  (implies (and (all-< x y)
                (consp x))
           (< (car x) y))
  :rule-classes :forward-chaining)

;; (defthmd <-of-car-when-all->
;;   (implies (and (all-> y x)
;;                 (consp y))
;;            (< x (car y))))

;move
(defund <-all (x y)
  (if (endp y)
      t
    (and (< x (first y))
         (<-all x (rest y)))))

(defthmd <-of-car-when-<-all
  (implies (and (<-all x y)
                (consp y))
           (< x (car y)))
  :hints (("Goal" :in-theory (enable <-all))))


(defthm <-all-of-append
  (equal (<-all a (append x y))
         (and (<-all a x)
              (<-all a y)))
  :hints (("Goal" :in-theory (e/d (<-all reverse-list) ()))))

(defthm <-all-of-reverse-list
  (equal (<-all a (reverse-list x))
         (<-all a x))
  :hints (("Goal" :in-theory (e/d (<-all reverse-list) ()))))

(defthm <-all-revappend
  (equal (<-all a (revappend x y))
         (and (<-all a x)
              (<-all a y)))
  :hints (("Goal" :in-theory (e/d (all-> revappend-lemma) ()))))

(defthm <-all-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (<-all a lst)
                (<-all a tail)
                (<-all a acc)
                (<= (len tail) (len lst))
                )
           (<-all a (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux <-all))))

(defthm <-all-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (<-all a lst)
                (<-all a tail)
                (<-all a acc)
                (<= (len tail) (len lst))
                )
           (<-all a (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux <-all))))

(defthm <-all-of-mv-nth-0-of-split-list-fast
  (implies (<-all a x)
           (<-all a (mv-nth 0 (split-list-fast x))))
  :hints (("Goal" :in-theory (enable split-list-fast <-all))))

(defthm <-all-of-mv-nth-1-of-split-list-fast
  (implies (<-all a x)
           (<-all a (mv-nth 1 (split-list-fast x))))
  :hints (("Goal" :in-theory (enable split-list-fast <-all))))

(defthm <-all-of-merge-<
  (equal (<-all a (merge-< l1 l2 acc))
         (and (<-all a l1)
              (<-all a l2)
              (<-all a acc)))
  :hints (("Goal" :in-theory (enable merge-< <-all))))

;todo: strengthen to an equal rule
(defthm <-all-of-merge-sort-<
  (implies (<-all a x)
           (<-all a (merge-sort-< x)))
  :hints (("Goal" :in-theory (enable merge-sort-< <-all))))

(defthm all->-becomes-<-all
  (equal (all-> x a)
         (<-all a x))
  :hints (("Goal" :in-theory (enable <-all all->))))


;move
(defthm <-all-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                ;(< n (alen1 dag-parent-array-name dag-parent-array))
                (natp n))
           (<-all n (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :use (:instance all->-of-aref1-when-dag-parent-arrayp)
           :in-theory (e/d (all->-becomes-<-all)
                           (all->-of-aref1-when-dag-parent-arrayp)))))



;; Maintains a worklist of ancestors of the target node, in sorted order.  The
;; first item on the worklist is always the smallest unhandled ancestor.  Every
;; node on the worklist depends on the target and must be rebuilt. Returns (mv
;; erp translation-array dag-array dag-len dag-parent-array dag-constant-alist
;; dag-variable-alist).
(defund rebuild-nodes-bottom-up (worklist ;ancestors (parents, etc.) of the target node, should be sorted, must all be function call nodes, since they have children
                                 translation-array ;maps each nodenum to nil (unhandled) or a nodenum (maybe the nodenum itself) [or a quotep - no, not currently]
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 ;old-dag-len
                                 )
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (no-duplicatesp-equal worklist) ;needed for termination
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
                  :measure (if (consp worklist)
                               (nfix (+ 1 (- (alen1 'translation-array translation-array) (first worklist))))
                             0)
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                           :in-theory (enable <-of-first-and-second-when-sortedp-and-no-duplicatesp-equal
                                              natp-of-cadr-when-all-natp
                                              WF-DAGP ;why?
                                              <-of-car-when-<-all
                                              )))
                  :guard-hints (("Goal" :in-theory (enable ALL-RATIONALP-WHEN-ALL-NATP
                                                           RATIONAL-LISTP-WHEN-ALL-NATP
                                                           wf-dagp)))
;                  :verify-guards nil ; done below
                  ))
  (if (or (endp worklist)
          (not (and (mbt (sortedp-<= worklist))
                    (mbt (all-natp worklist))
                    (mbt (all-< worklist dag-len))
                    (mbt (no-duplicatesp-equal worklist))
                    (mbt (all-< worklist (alen1 'translation-array translation-array)))
                    (mbt (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))
                    (mbt (array1p 'translation-array translation-array))
                    (mbt (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist))
                    (mbt (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
                    )))
      (mv (erp-nil) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((nodenum (first worklist))
           ;; NODENUM is the smallest unhandled ancestor.  Its children have all been handled.  So handle it now.
           (expr (aref1 'dag-array dag-array nodenum)))
      (if (or (atom expr) ;todo: get rid of this IF since the node must be a function call
              (fquotep expr))
          (prog2$ (er hard? 'rebuild-nodes-bottom-up "Unexpected ancestor: ~x0." expr)
                  (mv (erp-t) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
        ;; The node will always be a function call, so fix it up:
        (b* ((parents (aref1 'dag-parent-array dag-parent-array nodenum))
             ;; (- (cw "Node ~x0 has ~x1 parents: ~x2~%" nodenum (len parents) parents))
             ((when (not (all-< parents (alen1 'translation-array translation-array)))) ;todo: drop.  should always be true since these are nodes in the old dag
              (er hard? 'rebuild-nodes-bottom-up "Bad parents.")
              (mv (erp-t) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
             (new-args (maybe-translate-args (dargs expr) translation-array))
             ;; TODO: It would be nice to evaluate ground terms here,
             ;; but that could cause translation-array to map nodes to
             ;; things other than nodenums (which the callers would
             ;; need to handle -- e.g., if a literal maps to a quotep).
             ((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (add-function-call-expr-to-dag-array (ffn-symb expr) new-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
             ((when erp) (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
             (translation-array (aset1 'translation-array translation-array nodenum new-nodenum))
             (worklist (rest worklist)) ;; skip the current node
             (worklist (merge-<  ;todo: combine with the remove dups just below
                        (merge-sort-< parents) ;or could keep them sorted
                        worklist nil))
             (worklist (remove-duplicates-from-sorted-list worklist nil)))
          (rebuild-nodes-bottom-up worklist
                                   translation-array
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-bottom-up
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (sortedp-<= worklist)
                (no-duplicatesp-equal worklist) ;needed for termination
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (not (mv-nth 0 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-bottom-up))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-bottom-up
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (sortedp-<= worklist)
                (no-duplicatesp-equal worklist) ;needed for termination
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (not (mv-nth 0 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-bottom-up))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-bottom-up
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (sortedp-<= worklist)
                (no-duplicatesp-equal worklist) ;needed for termination
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux top-nodenum-to-check ;(+ -1 (alen1 'translation-array translation-array))
                                        translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (not (mv-nth 0 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (integerp top-nodenum-to-check)
                (< top-nodenum-to-check (alen1 'translation-array translation-array)))
           (translation-arrayp-aux top-nodenum-to-check (mv-nth 1 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-bottom-up) (natp)))))

(def-dag-builder-theorems
  (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
         (nat-listp worklist)
         (sortedp-<= worklist)
         (no-duplicatesp-equal worklist) ;needed for termination
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)))

;; (defthm natp-of-mv-nth-3-of-rebuild-nodes-bottom-up
;;   (implies (and (natp dag-len)
;;                 ;(wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                 ;(nat-listp worklist)
;;                 ;(sortedp-<= worklist)
;;                 ;(no-duplicatesp-equal worklist) ;needed for termination
;;                 ;(all-< worklist dag-len)
;;                 ;(array1p 'translation-array translation-array)
;;                 ;(translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
;;                 ;(all-< worklist (alen1 'translation-array translation-array))
;;                 ;(bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
;;                 ;(not (mv-nth 0 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
;;                 )
;;            (natp (mv-nth 3 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
;;   :hints (("Goal" :in-theory (e/d (rebuild-nodes-bottom-up) (natp)))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-bottom-up
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (sortedp-<= worklist)
                (no-duplicatesp-equal worklist) ;needed for termination
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                        translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                ;;(not (mv-nth 0 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                )
           (bounded-translation-arrayp-aux n
                                           (mv-nth 1 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                           (mv-nth 3 (rebuild-nodes-bottom-up worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-bottom-up))))

;; Returns (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; smashes 'translation-array (and 'tag-array ?)
;ffixme can the literal-nodenums returned ever contain a quotep?
;this could compute ground terms - but the caller would need to check for quoteps in the result
;doesn't change any existing nodes in the dag (just builds new ones)
;; TODO: Consider making a version of this for prover depth 0 which rebuilds
;; the array from scratch (since we can change existing nodes when at depth 0).
(defund rebuild-literals-with-substitution2 (literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             nodenum-to-replace
                                             new-nodenum ;fixme allow this to be a quotep?
                                             )
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (natp nodenum-to-replace)
                              (< nodenum-to-replace dag-len)
                              (natp new-nodenum)
                              (< new-nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (all-integerp-when-all-natp all-rationalp-when-all-natp)
                                                        (myquotep dargp dargp-less-than))))))
  (b* (;; One of these parents will be the equality we are using to subst, but it may occur elsewhere as well, so handle it normally:
       (parents (aref1 'dag-parent-array dag-parent-array nodenum-to-replace))
       ;; (- (cw "Node ~x0 being replaced has ~x1 parents: ~x2.~%" nodenum-to-replace (len parents) parents))
       (translation-array (make-empty-array 'translation-array dag-len)) ;can we make it any shorter?
       ;; ensure that nodenum-to-replace gets replaced with new-nodenum:
       (translation-array (aset1 'translation-array translation-array nodenum-to-replace new-nodenum))
       ((mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        ;;todo: drop the call to remove-duplicates-from-sorted-list if we can ensure parent lists never contain dups
        (rebuild-nodes-bottom-up (remove-duplicates-from-sorted-list (merge-sort-< parents) nil) ;; initial worklist
                                 translation-array
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((when erp) (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((mv changed-literal-nodenums
            unchanged-literal-nodenums)
        (maybe-translate-nodes literal-nodenums
                               translation-array
                               ;; Initialize accumulator to include all uneffected nodes
                               nil nil)))
    (mv (erp-nil)
        ;; We put the changed nodes first, in the hope that we will use them to
        ;; substitute next, creating a slightly larger term, and so on.  The
        ;; unchanged-literal-nodenums here got reversed wrt the input, so if
        ;; we had a bad ordering last time, we may have a good ordering this
        ;; time:
        (append changed-literal-nodenums unchanged-literal-nodenums)
        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm len-of-mv-nth-1-of-rebuild-literals-with-substitution2
  (implies (not (mv-nth 0 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
           (equal (len (mv-nth 1 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                  (len literal-nodenums)))
  :hints (("Goal" :in-theory (enable rebuild-literals-with-substitution2))))

(local (in-theory (enable all-integerp-when-all-natp
                          natp-of-+-of-1-alt))) ;for the call of def-dag-builder-theorems just below

(local (in-theory (disable natp)))

(def-dag-builder-theorems
  (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)
  (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((nat-listp literal-nodenums)
         (all-< literal-nodenums dag-len)
         (natp nodenum-to-replace)
         (< nodenum-to-replace dag-len)
         (natp new-nodenum)
         (< new-nodenum dag-len)))

;gen?
(defthm nat-listp-of-mv-nth-1-of-rebuild-literals-with-substitution2
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp nodenum-to-replace)
                (< nodenum-to-replace dag-len)
                (nat-listp acc)
                (natp new-nodenum)
                (< new-nodenum dag-len)
                ;; (not (mv-nth 0 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                )
           (nat-listp (mv-nth 1 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution2 reverse-becomes-reverse-list wf-dagp)
                                  (;REVERSE-REMOVAL
                                   natp)))))

(defthm true-listp-of-mv-nth-1-of-rebuild-literals-with-substitution2
  (implies (true-listp literal-nodenums)
           (true-listp (mv-nth 1 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution2 reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))

(defthm all-<-of-mv-nth-1-of-rebuild-literals-with-substitution2
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp nodenum-to-replace)
                (< nodenum-to-replace dag-len)
                (nat-listp acc)
                (natp new-nodenum)
                (< new-nodenum dag-len)
                ;; (not (mv-nth 0 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                (all-< acc dag-len)
                )
           (all-< (mv-nth 1 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))
                  (mv-nth 3 (rebuild-literals-with-substitution2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution2 reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))
