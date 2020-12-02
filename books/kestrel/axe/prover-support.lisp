; Supporting utilities for the Axe Prover(s)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/utilities/split-list-fast" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/utilities/make-cons-nest" :dir :system)
(include-book "kestrel/utilities/conjuncts-and-disjuncts" :dir :system) ; for negate-terms
(include-book "all-less-than-or-equal")
(include-book "merge-sort-less-than")
(include-book "supporting-nodes")
(include-book "dag-array-builders")
(include-book "renaming-array")
(include-book "translation-array")
(include-book "unify-tree-and-dag")
(include-book "dag-array-printing")
(include-book "merge-term-into-dag-array-basic")
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "def-dag-builder-theorems")
(include-book "supporting-vars")
(include-book "crunch-dag2")
(include-book "worklists")
(include-book "make-var-names")
(include-book "dag-size2") ; for size-array-for-sorted-nodes
(include-book "misc/records" :dir :system) ; for axe-prover-hints, todo
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
;trim?:
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
;(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local
 (defthm equal-of-len-of-remove-equal-same
   (equal (equal (len (remove-equal a x)) (len x))
          (not (member-equal a x)))))

(local
 (defthm rationalp-when-integerp
   (implies (integerp x)
            (rationalp x))))

;dup in prove-with-stp
(defthm assoc-equal-when-member-equal-of-strip-cars
  (implies (and (member-equal key (strip-cars alist))
                (or key (alistp alist)))
           (assoc-equal key alist))
  :hints
  (("Goal" :in-theory (e/d (member-equal assoc-equal strip-cars alistp) nil))))

;dup
(defthmd natp-of-+-of-1-alt
  (implies (integerp x)
           (equal (natp (+ 1 x))
                  (<= -1 x))))

;dup
(defthmd consp-when-<-of-0-and-nth
  (implies (< 0 (NTH n x))
           (consp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm integerp-of-car-of-last-when-all-natp
  (implies (and (all-natp x)
                (consp x))
           (integerp (car (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defthm <=-of-0-and-car-of-last-when-all-natp
  (implies (and (all-natp x)
                (consp x))
           (<= 0 (car (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defthm <-of--1-and-car-of-last-when-all-natp
  (implies (and (all-natp x)
                (consp x))
           (< -1 (car (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defthm <-of-car-of-last-and--1-when-all-natp
  (implies (and (all-natp x)
                (consp x))
          (not  (< (car (last x)) -1)))
  :hints (("Goal" :in-theory (enable last))))

(defthm all-<-of-+-of-1
  (implies (and (syntaxp (not (quotep y)))
                (all-integerp x)
                (integerp y))
           (equal (all-< x (+ 1 y))
                  (all-<= x y)))
  :hints (("Goal" :in-theory (enable all-<= all-<))))

(defund all-<=-all (x y)
  (if (endp y)
      t
    (and (all-<= x (first y))
         (all-<=-all x (rest y)))))

(defthm all-<=-of-car-of-last
  (implies (and (all-<=-all x y)
                (consp y))
           (all-<= x (car (last y))))
  :hints (("Goal" :in-theory (enable all-<= all-<=-all))))

(defthm all-<=-all-of-append
  (equal (all-<=-all x (append y1 y2))
         (and (all-<=-all x y1)
              (all-<=-all x y2)))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm all-<=-all-of-reverse-list-arg2
  (equal (all-<=-all x (reverse-list y))
         (all-<=-all x y))
  :hints (("Goal" :in-theory (enable all-<=-all reverse-list))))

(defthm all-<=-all-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-<=-all x lst)
                ;;(all-<=-all x tail)
                (<= (len tail) (len lst))
                (all-<=-all x acc))
           (all-<=-all x (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux all-<=-all))))

(defthm all-<=-all-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (all-<=-all x lst)
                ;;(all-<=-all x tail)
                (<= (len tail) (len lst))
                (all-<=-all x acc))
           (all-<=-all x (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux all-<=-all))))

(defthm all-<=-all-of-mv-nth-0-of-split-list-fast
  (implies (all-<=-all x l)
           (all-<=-all x (mv-nth 0 (split-list-fast l))))
  :hints (("Goal" :in-theory (enable split-list-fast all-<=-all))))

(defthm all-<=-all-of-mv-nth-1-of-split-list-fast
  (implies (all-<=-all x l)
           (all-<=-all x (mv-nth 1 (split-list-fast l))))
  :hints (("Goal" :in-theory (enable split-list-fast all-<=-all))))

(defthm all-<=-all-of-merge-<
  (implies (and (all-<=-all x l1)
                (all-<=-all x l2)
                (all-<=-all x acc))
           (all-<=-all x (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<
                                     ;;revappend-lemma
                                     all-<=-all))))

(defthm all-<=-all-of-merge-sort-<
  (implies (all-<=-all x l)
           (all-<=-all x (merge-sort-< l)))
  :hints (("Goal" :in-theory (enable merge-sort-< all-<=-all))))

(defun sortedp-<= (x)
  (declare (xargs :guard (rational-listp x)))
  (if (endp x)
      t
    (if (endp (rest x))
        t
      (and (<= (first x) (second x)) ;allows dups
           (sortedp-<= (rest x))))))

;todo: nested induction
(defthm all-<=-of-car-of-last-when-sortedp-<=
  (implies (sortedp-<= x)
           (all-<= x (car (last x))))
  :hints (("Goal" :in-theory (enable ALL-<=))))

(defun <=-all (x y)
  (if (endp y)
      t
    (and (<= x (first y))
         (<=-all x (rest y)))))

(defthmd all-<=-all-redef
  (implies (consp x)
           (equal (all-<=-all x y)
                  (and (all-<=-all (cdr x) y)
                       (<=-all (car x) y))))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm <=-all-trans-1
  (implies (and (<=-all x2 lst)
                (<= x x2))
           (<=-all x lst))
  :hints (("Goal" :in-theory (enable <=-all))))

(defthm all-<=-all-when-not-consp-arg1
  (implies (not (consp x))
           (all-<=-all x y))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm ALL-<=-ALL-when-not-consp-arg2
  (implies (not (consp y))
           (ALL-<=-ALL x y))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm sortedp-<=-of-append
  (equal (sortedp-<= (append x y))
         (and (sortedp-<= x)
              (sortedp-<= y)
              (all-<=-all x y)))
  :hints (("Goal" :in-theory (enable all-<=-all-redef all-<= append))))

(defthm all-<=-of-reverse-list-arg1
  (equal (all-<= (reverse-list x) y)
         (all-<= x y))
  :hints (("Goal" :in-theory (enable all-<=))))

(defthm all-<=-all-of-reverse-list-arg1
  (equal (all-<=-all (reverse-list x) y)
         (all-<=-all x y))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm all-<=-all-of-cons-arg1
  (equal (all-<=-all (cons x1 x2) lst)
         (and (<=-all x1 lst)
              (all-<=-all x2 lst)))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm <=-all-when-sortedp-<=-and-<=-of-car
  (implies (and (SORTEDP-<= lst)
                (<= x (CAR lst)))
           (<=-ALL x lst))
  :hints (("Goal" :in-theory (enable <=-ALL))))

(defthm ALL-<=-ALL-of-cdr-arg2
  (implies (ALL-<=-ALL ACC L2)
           (ALL-<=-ALL ACC (CDR L2)))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm ALL-<=-ALL-of-cons-arg2
  (equal (ALL-<=-ALL x (cons a lst))
         (and (ALL-<= x a)
              (ALL-<=-ALL x lst)))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm sorted-of-merge-<
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2)
                (sortedp-<= (reverse-list acc))
                (all-<=-all acc l1)
                (all-<=-all acc l2)
                )
           (sortedp-<= (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<
                                     ;;revappend-lemma
                                     ))))

(defthm sortedp-<=-of-merge-sort-<
  (sortedp-<= (merge-sort-< x))
  :hints (("Goal" :in-theory (enable merge-sort-<))))

(defthm all-<=-of-car-of-last-when-sortedp-<=-2
  (implies (and (sortedp-<= x)
                (subsetp-equal y x))
           (all-<= y (car (last x))))
  :hints (("Goal" :in-theory (enable ALL-<= SUBSETP-EQUAL))))

(encapsulate ()
  (local (include-book "kestrel/lists-light/memberp" :dir :system))
;move
  (defcong perm iff (member-equal x y) 2
    :hints (("Goal" :in-theory (enable member-equal perm)))))

;move
(defcong perm equal (subsetp-equal x y) 2
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-merge-sort-<
  (equal (subsetp-equal x (merge-sort-< x))
         (subsetp-equal x x)))

;;move to rational-lists.lisp
(defthm all-<=-of-maxelem
  (all-<= lst (maxelem lst))
  :hints (("Goal" :in-theory (enable all-<=))))

(defcong perm equal (all-<=-all x y) 1
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))


;; (defcong perm equal (all-<=-all x y) 2
;;   :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm all-<=-all-of-merge-sort-<-strong
  (equal (all-<=-all (merge-sort-< x) y)
         (all-<=-all x y))
  :hints (("Goal" :in-theory (enable merge-sort-<))))

(defun keep-non-atoms (items)
  (declare (xargs :guard t))
  (if (atom items) ;would endp be faster here?
      nil
    (if (atom (car items))
        (keep-non-atoms (cdr items))
      (cons (car items) (keep-non-atoms (cdr items))))))

;not tail recursive
;often lst will be sorted, but really the sortedness isn't crucial, just that equal elements are all grouped together
(defun remove-duplicates-from-grouped-list (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      nil
    (if (endp (cdr lst))
        lst
      (let ((elem (car lst)))
        (if (equal elem (car (cdr lst)))
            (remove-duplicates-from-grouped-list (cdr lst))
          (cons elem
                (remove-duplicates-from-grouped-list (cdr lst))))))))

(defthm true-listp-of-remove-duplicates-from-grouped-list
  (implies (true-listp lst)
           (true-listp (remove-duplicates-from-grouped-list lst))))

(defthm eqlable-listp-of-remove-duplicates-from-grouped-list
  (implies (eqlable-listp lst)
           (eqlable-listp (remove-duplicates-from-grouped-list lst))))

(defthm all-natp-of-remove-duplicates-from-grouped-list
  (implies (all-natp x)
           (all-natp (remove-duplicates-from-grouped-list x))))

(defthm all-<-of-remove-duplicates-from-grouped-list
  (equal (all-< (remove-duplicates-from-grouped-list x) bound)
         (all-< x bound)))

;why are these firing?
;; (local (in-theory (disable bag::not-subbagp-of-cons-from-not-subbagp
;;                            bag::subbagp-of-remove-1-irrel
;;                            bag::subbagp-of-cons
;;                            bag::subbagp-memberp-remove-1
;;                            bag::memberp-x-remove-x-implies-memberp-x-remove-1-y
;;                            list::member-eq-is-memberp-propositionally)))

;;(defconst *store-constants-inline* t) ;bozo consider changing this?

;; ;fixme enable this and always go to add-to-set-equal?
;; (defthmd add-to-set-eql-becomes-add-to-set-equal
;;   (equal (add-to-set-eql x l)
;;          (add-to-set-equal x l))
;;   :hints (("Goal" :in-theory (enable add-to-set-eql add-to-set-equal))))

;; ;eventually have the evaluator check if it's a ground term too..
;; (make-event
;;  (make-evaluator 'axe-evaluator2
;;                  (axe-evaluator-function-info) ;(cons '(apply-AXE-EVALUATOR2 arg1 arg2 arg3) )  ;what else?
;;                  t                ;args are quoted (fffixme does this cause lots of quoting and unquoting as the evaluator computes?
;;   ;               :make-term       ;if can't eval, just make the term
;;    ;              t                ; quote the result
;;                  ))

;; ;fixme deprecate this?
;; (make-event
;;  (make-evaluator 'axe-evaluator3
;;                  (cons '(DAG-VAL-WITH-AXE-EVALUATOR arg1 arg2 arg3 arg4 ;(+ 1 array-depth)
;;                                                      ) ;what else?
;;                        (axe-evaluator-function-info)) ;(cons '(apply-AXE-EVALUATOR2 arg1 arg2 arg3) )
;;                  t                             ;args are quoted
;; ;             :nil       ;if can't eval, just return nil
;; ;            t          ; quote the result
;;                  ))

(defthm not-myquotep-when-len-wrong
  (implies (and (equal len (len x))
                (not (equal 2 len)))
           (not (myquotep x))))

(defthmd consp-of-cdr-when-pseudo-termp
  (implies (and (pseudo-termp term)
                (equal 'quote (car term)))
           (consp (cdr term))))

;; BOZO - where else might we want to handle lambdas?  pre-expand lambdas in rules?

;BOZO put back provisional adding of nodes for hyps (but what if we want to memoize them?)
;BOZO put back in depth2 (rewrite stack depth) limiting?  or is everything tail recursive now?

;move this stuff!

;; (thm
;;  (implies (and (MY-ALL-QUOTEPS ITEMS)
;;                (natp n)
;;                (< n (len items)))
;;           (< 1 (len (nth n items)))) ;todo: would like to say it's 2
;;  :hints (("Goal" :in-theory (e/d (nth) (NTH-OF-CDR)))))


;; (thm
;;  (implies (and (MY-ALL-QUOTEPS ITEMS)
;;                (natp n)
;;                (< n (len items)))
;;           (< 1 (len (nth n items)))) ;todo: would like to say it's 2
;;  :hints (("Goal" :in-theory (e/d (nth) (NTH-OF-CDR)))))

;; (thm
;;  (implies (and (PSEUDO-DAG-ARRAYP-AUX 'DAG-ARRAY DAG-ARRAY ITEM)
;;                (CONSP (AREF1 'DAG-ARRAY DAG-ARRAY ITEM))
;;                (not (equal 'quote (NTH 0 (AREF1 'DAG-ARRAY DAG-ARRAY ITEM))))
;;                )
;;           (< (LARGEST-NON-QUOTEP (CDR (AREF1 'DAG-ARRAY DAG-ARRAY ITEM)))
;;              item))
;;  :hints (("Goal" :in-theory (enable PSEUDO-DAG-ARRAYP-AUX))))

(defun make-var-lookup-terms (vars alist-nodenum)
  (declare (xargs :guard (true-listp vars)))
  (if (endp vars)
      nil
    (cons `(lookup-equal ',(car vars) ,alist-nodenum)
          (make-var-lookup-terms (cdr vars) alist-nodenum))))

;; (defun lookup-lst (lst alist)
;;   (declare (xargs :guard (and (alist-with-integer-keysp alist)
;;                               (all-integerp lst))))
;;   (if (atom lst)
;;       nil
;;       (cons (lookup (car lst) alist)
;;             (lookup-lst (cdr lst) alist))))

;; ;;known-predicates are items of the form <nodenum> or (not <nodenum>):
;; ;returns a list of terms
;; (defun get-extra-assumptions (known-predicates predicate-nodenum-term-alist)
;;   (if (endp known-predicates)
;;       nil
;;     (let ((predicate (car known-predicates)))
;;       (cons (if (and (consp predicate)
;;                      ;(eq 'not (ffn-symb predicate)) ;if it's a consp it must be a not
;;                      )
;;                 `(not ,(lookup (first (fargs predicate)) predicate-nodenum-term-alist))
;;               (lookup predicate predicate-nodenum-term-alist))
;;             (get-extra-assumptions (cdr known-predicates) predicate-nodenum-term-alist)))))

;; (skip- proofs (verify-guards get-extra-assumptions))

;(local (in-theory (enable natp)))

;; copies a segment of nodes from FROM-DAG-ARRAY to DAG-ARRAY and returns the new dag (including the auxiliary data structures) and a RENAMING-ARRAY
;; Returns (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array).
;fixme should this use a worklist instead of copying a segment?
(defun add-array-nodes-to-dag (nodenum max-nodenum
                                       from-dag-array-name from-dag-array from-dag-array-len
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       renaming-array)
  (declare ;(type (integer 0 2147483646) dag-len)
;(type (integer 0 2147483645) nodenum)
;(type (integer -1 2147483645) max-nodenum)
   (xargs :measure (nfix (+ 1 (- max-nodenum nodenum)))
          :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                      (integerp max-nodenum)
                      (natp nodenum)
                      (pseudo-dag-arrayp from-dag-array-name from-dag-array from-dag-array-len)
                      (< max-nodenum from-dag-array-len)
                      (<= nodenum (+ 1 max-nodenum))
                      (pseudo-dag-arrayp from-dag-array-name from-dag-array (+ 1 max-nodenum))
                      (renaming-arrayp 'renaming-array renaming-array nodenum) ;todo: add more guards?
                      (<= (+ 1 max-nodenum)
                          (alen1 'renaming-array renaming-array))
                      (bounded-renaming-entriesp (+ -1 nodenum) 'renaming-array renaming-array dag-len))
          :guard-hints (("Goal" :in-theory (e/d (not-cddr-when-dag-exprp0-and-quotep
                                                 renaming-arrayp ;todo
                                                 )
                                                (pseudo-dag-arrayp))))))
  (if (or (not (mbt (natp nodenum)))
          (not (mbt (integerp max-nodenum)))
          (< max-nodenum nodenum))
      (mv (erp-nil) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
    (let* ((expr (aref1 from-dag-array-name from-dag-array nodenum)))
      (if (variablep expr)
          (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (add-variable-to-dag-array expr dag-array dag-len
                                             dag-parent-array ;;just passed through
                                             dag-constant-alist ;;just passed through
                                             dag-variable-alist)
            (if erp
                (mv erp nil nil nil nil nil nil)
              (add-array-nodes-to-dag (+ 1 nodenum) max-nodenum from-dag-array-name from-dag-array from-dag-array-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      (aset1 'renaming-array renaming-array nodenum new-nodenum))))
        (if (quotep expr)
            (add-array-nodes-to-dag (+ 1 nodenum) max-nodenum from-dag-array-name from-dag-array from-dag-array-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    (aset1 'renaming-array renaming-array nodenum expr))
          ;;regular function call:
          (let* ((args (dargs expr))
                 (args (rename-args args 'renaming-array renaming-array)))
            (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (add-function-call-expr-to-dag-array (ffn-symb expr) args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (if erp
                  (mv erp nil nil nil nil nil nil)
                (add-array-nodes-to-dag (+ 1 nodenum) max-nodenum from-dag-array-name from-dag-array from-dag-array-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        (aset1 'renaming-array renaming-array nodenum new-nodenum))))))))))

;;
;; tags (part 1, since currently get-node-tag is used in the context stuff - change that?! maybe i already did?)
;;

(in-theory (disable maxelem acons))

(defthm integerp-of-maxelem-when-all-integerp-cheap
  (implies (and (consp nodenums)
                (ALL-INTEGERP NODENUMS))
           (INTEGERP (MAXELEM NODENUMS)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable maxelem all-integerp))))

(defthmd integerp-of-maxelem-when-all-integerp
  (implies (and (consp nodenums)
                (ALL-INTEGERP NODENUMS))
           (INTEGERP (MAXELEM NODENUMS)))
  :hints (("Goal" :in-theory (enable maxelem all-integerp))))

;; (thm
;;  (implies (and (all-< items x)
;;                (consp items))
;;           (all-< (maxelem items) x))
;;  :hints (("Goal" :in-theory (enable all-< maxelem))))


(defthmd <-of-car-when-all-<
  (implies (and (all-< items x)
                (consp items))
           (< (car items) x))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm <-of-car-when-all-<-cheap
  (implies (and (all-< items x)
                (consp items))
           (< (car items) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable all-<))))


;yuck?
(defthm <-of-maxelem-of-cdr-when-all-<
  (implies (and (all-< items x)
                (< 1 (len items)))
           (< (maxelem (cdr items)) x))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm rational-of-car--when-all-natp-cheap
  (implies (and (all-natp items)
                (consp items))
           (rationalp (car items)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable all-natp rational-listp))))

(defthm all-<-hack
  (implies (and (all-< items bound)
                (all-integerp items)
                (integerp bound)
                (consp items))
           (not (< bound (binary-+ 1 (car items))))))

(defthm all-natp-implies-all-integerp-cheap
  (implies (all-natp x)
           (all-integerp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-natp all-integerp))))

;; ;get the nodenums of all predicates that are the tests of an IF (or MYIF or BOOLIF or BVIF) - fffffixme what about booland and boolor?
;; ;now only counts predicates that are not probably equal to a constant or lower node
;; (defun get-tested-predicate-nodenums (nodenum dag-array-name dag-array acc tag-array2)
;;   (declare (xargs :measure (nfix (+ 1 nodenum))
;;                   :hints (("Goal" :in-theory (enable natp)))
;;                   :verify-guards nil
;;                   :guard (and (ARRAY1P 'TAG-ARRAY2 TAG-ARRAY2)
;;                               (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
;;                               (true-listp acc))))
;;   (if (not (natp nodenum))
;;       acc
;;     (let* ((expr (aref1 dag-array-name dag-array nodenum)))
;;       (if (or (variablep expr)
;;               (fquotep expr))
;;           (get-tested-predicate-nodenums (+ -1 nodenum) dag-array-name dag-array acc tag-array2)
;;         (let* ((fn (ffn-symb expr))
;;                (args (fargs expr))
;;                (tested-pred (and (consp expr)
;;                                  (cond ((and (or (eq 'if fn)
;;                                                  (eq 'myif fn)
;;                                                  (eq 'boolif fn))
;;                                              (consp args)
;;                                              (natp (first args)) ;makes sure it's not a quotep
;;                                              )
;;                                         (first args))
;;                                        ((and (eq 'bvif fn)
;;                                              (consp args)
;;                                              (consp (cdr args))
;;                                              (natp (second args)))
;;                                         (second args))
;;                                        (t nil))))
;;                (acc (if (and tested-pred
;;                              (or (not tag-array2)
;;                                  (and (not (get-node-tag tested-pred *probable-constant* tag-array2))
;;                                       (not (get-node-tag tested-pred *smaller-nodes-that-might-be-equal* tag-array2)))))
;;                         (add-to-set-eql tested-pred acc) ;could this be expensive?  could keep an array and mark each tested predicate and then harvest the marked nodes
;;                       acc)))
;;           (get-tested-predicate-nodenums (+ -1 nodenum) dag-array-name dag-array acc tag-array2))))))

;; (skip- proofs (verify-guards get-tested-predicate-nodenums))

;; (defmap aref1-list (array-name array indices) (aref1 array-name array indices) :fixed (array-name array))

;; (skip- proofs (verify-guards aref1-list)) ;move

;a context-indicator is for one node and predicate and is one of these (t), (t nil), (nil), or ().

;; ;walk through PARENT-EXPRS and PARENT-CONTEXT-INDICATOR-LISTS in sync, updating t-via-all-parents-so-far and nil-via-all-parents-so-far
;; (defun make-context-indicator-for-pred (nodenum predicate-nodenum predicate-num parent-exprs parent-context-indicator-lists t-via-all-parents-so-far nil-via-all-parents-so-far)
;; ;;   (declare (xargs :guard (and (true-listp parent-exprs)
;; ;;                               (integerp predicate-nodenum)
;; ;;                               (natp predicate-num)
;; ;;                               (ALL-TRUE-LISTP parent-context-indicator-lists)
;; ;;                               (true-listp parent-context-indicator-lists)
;; ;;                               (true-list parent-context-indicator-lists))))
;;   (if (endp parent-exprs)
;;       (if t-via-all-parents-so-far
;;           (if nil-via-all-parents-so-far
;;               '(t nil)
;;             '(t))
;;         (if nil-via-all-parents-so-far
;;             '(nil)
;;           '()))
;;     (let* ((parent-expr (car parent-exprs))
;;            (parent-context-indicator-list (car parent-context-indicator-lists)))
;;       (make-context-indicator-for-pred
;;        nodenum
;;        predicate-nodenum
;;        predicate-num
;;        (cdr parent-exprs)
;;        (cdr parent-context-indicator-lists)
;;        (and t-via-all-parents-so-far
;;             ;;either the predicate must be known true at the parent ..
;;             (or (member-eq t (nth predicate-num parent-context-indicator-list))
;;                 ;; ... or the parent is an ITE with the pred as the test and the
;;                 ;; nodenum in the then branch (but not in the else branch)
;;                 (let ((fn (ffn-symb parent-expr))) ;;(parent expr must be a cons, so no need to check consp)
;;                   (and (member-eq fn '(if myif boolif bvif)) ;would an or here be faster?
;;                        (let ((args (fargs parent-expr)))
;;                          (and (eql predicate-nodenum (if-test fn args))
;;                               (eql nodenum (if-then-branch fn args))
;;                               (not (eql nodenum (if-else-branch fn args)))
;;                               (or (not (eq 'bvif fn))
;;                                   (not (eql nodenum (first args))))
;;                               ))))))
;; ;this can redo some of the operations above (e.g., the nth):
;;        (and nil-via-all-parents-so-far
;;             ;;either the predicate must be known false at the parent ...
;;             (or (member-eq nil (nth predicate-num parent-context-indicator-list))
;;                 ;; ... or the parent is an ITE with the pred as the test and the
;;                 ;; nodenum in the else branch (but not in the then branch)
;;                 (let ((fn (ffn-symb parent-expr))) ;;(parent expr must be a cons, so no need to check consp)
;;                   (and (member-eq fn '(if myif boolif bvif)) ;would an or here be faster?
;;                        (let ((args (fargs parent-expr)))
;;                          (and (eql predicate-nodenum (if-test fn args))
;;                               (eql nodenum (if-else-branch fn args))
;;                               (not (eql nodenum (if-then-branch fn args)))
;;                               (or (not (eq 'bvif fn))
;;                                   (not (eql nodenum (first args))))))))))))))

;; (skip- proofs (verify-guards make-context-indicator-for-pred))

;; ;walks through the predicates, making the context-indicator for nodenum for each pred
;; ;should this cdr the elements of parent-context-indicator-lists (then dont do the nths above)?
;; (defun make-context-indicator-list-for-nodenum (nodenum predicate-nodenums predicate-num parent-exprs parent-context-indicator-lists acc)
;;   (if (endp predicate-nodenums)
;;       (reverse acc)
;;     (let* ((predicate-nodenum (car predicate-nodenums))
;;            (context-indicator-for-this-pred (make-context-indicator-for-pred nodenum predicate-nodenum predicate-num parent-exprs
;;                                                                              parent-context-indicator-lists
;;                                                                              t ;t-via-all-parents-so-far (true since we've processed no parents yet)
;;                                                                              t ;nil-via-all-parents-so-far (true since we've processed no parents yet)
;;                                                                              )))
;;       (make-context-indicator-list-for-nodenum nodenum
;;                                                (cdr predicate-nodenums) (+ 1 predicate-num) parent-exprs parent-context-indicator-lists
;;                                                (cons context-indicator-for-this-pred acc)))))

;; (skip- proofs (verify-guards make-context-indicator-list-for-nodenum))

;; ;walk down from the root, making the context-indicator-list of each node from the contexts of its parents
;; ;the context-indicator-list for a node is a list, with elements corresponding to the predicates at predicate-nodenums
;; ;each context-indicator is one of the following 4 things:
;; ;(t) means the predicate is known to be true for the node (all paths from the root to the node pass through the "then branch" of an ITE with the predicate as the if-test)
;; ;(nil) means the predicate is known to be false for the node (all paths from the root to the node pass through the "else branch" of an ITE with the predicate as the if-test)
;; ;() means we don't know anything about that prediate on the node
;; ;(t nil) is possible and means that the node is "unreachable" from the root (all paths pass through both an else branch and a then branch and the node's value is irrelevant, so we can rewrite it any way we want??) --ffixme what if it's reachable along other paths? <- huh?
;; (defun make-context-indicator-list-array-aux (nodenum dag-array-name dag-array dag-parent-array context-indicator-list-array predicate-nodenums)
;;   (declare (xargs :measure (nfix (+ 1 nodenum))
;;                   :hints (("Goal" :in-theory (enable natp)))))
;;   (if (not (natp nodenum))
;;       context-indicator-list-array
;;     (let* ((parent-nodenums (aref1 'dag-parent-array dag-parent-array nodenum))
;;            ;;do we have to do all of these lookups?
;;            (parent-exprs (aref1-list dag-array-name dag-array parent-nodenums))
;;            (parent-context-indicator-lists (aref1-list 'context-indicator-list-array context-indicator-list-array parent-nodenums))
;;            (context-indicator-list (make-context-indicator-list-for-nodenum nodenum predicate-nodenums 0 parent-exprs parent-context-indicator-lists nil)))
;;       (make-context-indicator-list-array-aux (+ -1 nodenum)
;;                                              dag-array-name
;;                                              dag-array
;;                                              dag-parent-array
;;                                              (aset1-safe 'context-indicator-list-array context-indicator-list-array nodenum context-indicator-list)
;;                                              predicate-nodenums))))

;; (skip- proofs (verify-guards make-context-indicator-list-array-aux))

;; ;dag-array should have no gaps?
;; ;returns (mv predicate-nodenums  ;nodenums of all predicates tested in if tests (if the right rules are on, these should not be calls to not?)
;; ;            context-indicator-list-array ;associates each nodenum with a context-indicator-list (one context-indicator for each predicate-nodenum)
;; ;            )
;; (defun make-context-indicator-list-array-helper (dag-array-name dag-array dag-len dag-parent-array tag-array2)
;;   (let* ((top-nodenum (+ -1 dag-len)) ;sure to be the top nodenum?
;;          (predicate-nodenums (get-tested-predicate-nodenums top-nodenum dag-array-name dag-array nil tag-array2))
;;          (context-indicator-list-array (make-empty-array 'context-indicator-list-array dag-len))
;;          (context-indicator-list-array (aset1-safe 'context-indicator-list-array
;;                                               context-indicator-list-array
;;                                               top-nodenum
;;                                               (repeat (len predicate-nodenums) nil) ;for the top node, for each predicate, we don't know anything about it...
;;                                               ))
;;          (context-indicator-list-array (make-context-indicator-list-array-aux (+ -1 top-nodenum) ;skip the top node
;;                                                                               dag-array-name
;;                                                                               dag-array dag-parent-array context-indicator-list-array predicate-nodenums)))
;;     (mv predicate-nodenums context-indicator-list-array)))

;; (skip- proofs (verify-guards make-context-indicator-list-array-helper))

;; ;this one takes a dag-array
;; ;returns (mv predicate-nodenums context-array)
;; (defun make-context-indicator-list-array (dag-array-name dag-array dag-len tag-array2)
;;   (mv-let (dag-parent-array dag-constant-alist dag-variable-alist) ;fixme don't need these last 2
;;           (make-dag-indices dag-array-name dag-array 'dag-parent-array dag-len) ;ffixme use a different name for the parent array?
;;           (declare (ignore dag-constant-alist dag-variable-alist))
;;           (make-context-indicator-list-array-helper dag-array-name dag-array dag-len dag-parent-array tag-array2)))

;; (skip- proofs (verify-guards make-context-indicator-list-array))

;; ;returns (mv predicate-nodenums  ;nodenums of all predicates tested in if tests (if the right rules are on, these should not be calls to not?)
;; ;            context-indicator-list-array ;associates each nodenum with a context-indicator-list (one context-indicator for each predicate-nodenum)
;; ;            )
;; ;this one takes a dag-lst
;; ;smashes array 'dag-array-name-for-make-context-indicator-list - also the parent array?  what else?
;; (defun make-context-indicator-lists (dag-lst dag-len tag-array2)
;;   (let* ((dag-array-name 'dag-array-name-for-make-context-indicator-lists)
;;          (dag-array (make-into-array dag-array-name dag-lst)))
;;     (make-context-indicator-list-array dag-array-name dag-array dag-len tag-array2)))

;(skip- proofs (verify-guards make-context-indicator-lists))

;; ;walks down CONTEXT-INDICATOR-LIST and PREDICATE-NODENUMS in sync
;; ;returns a context (a list of items of the form <nodenum> or (not <nodenum>))
;; (defun make-context-from-context-indicator-list (context-indicator-list predicate-nodenums)
;;   (if (endp context-indicator-list)
;;       nil
;;     (let ((context-indicator (first context-indicator-list))
;;           (predicate-nodenum (first predicate-nodenums)))
;;       ;;ffffixme handle unreachable nodes (those with entry (t nil), which i guess we can rewrite any way we want - or not rewrite at all?)?
;;       (if (equal context-indicator '(t))
;;           (cons predicate-nodenum (make-context-from-context-indicator-list (rest context-indicator-list) (rest predicate-nodenums)))
;;         (if (equal context-indicator '(nil))
;;             (cons `(not ,predicate-nodenum) (make-context-from-context-indicator-list (rest context-indicator-list) (rest predicate-nodenums)))
;;           (make-context-from-context-indicator-list (rest context-indicator-list) (rest predicate-nodenums)))))))

;; (skip- proofs (verify-guards make-context-from-context-indicator-list))

;; ;make context-indicator-list-array into a context-array
;; ;returns context-array, which associates nodenums with their contexts (lists of items of the form <nodenum> or (not <nodenum>))
;; (defun make-context-array-aux (n context-indicator-list-array context-array predicate-nodenums array-name)
;;   (declare (xargs :measure (nfix (+ 1 n))
;;                   :hints (("Goal" :in-theory (enable natp)))))
;;   (if (not (natp n))
;;       context-array
;;     (let* ((context-indicator-list (aref1 'context-indicator-list-array context-indicator-list-array n))
;;            (context (make-context-from-context-indicator-list context-indicator-list predicate-nodenums)))
;;       (make-context-array-aux (+ -1 n) context-indicator-list-array
;;                               (aset1-safe array-name context-array n context)
;;                               predicate-nodenums
;;                               array-name))))

;; (skip- proofs (verify-guards make-context-array-aux))

;; ;returns context-array, which associates nodenums with their contexts (lists of items of the form <nodenum> or (not <nodenum>))
;; ;add an option to only handle nodes above some min-nodenum?
;; (defun make-context-array (dag-lst dag-len array-name tag-array2)
;;   (mv-let (predicate-nodenums context-indicator-list-array)
;;           (make-context-indicator-lists dag-lst dag-len tag-array2)
;;           (make-context-array-aux (+ -1 dag-len) context-indicator-list-array (make-empty-array array-name dag-len) predicate-nodenums array-name)))

;(skip- proofs (verify-guards make-context-array))

;; ;returns context-array, which associates nodenums with their predicate lists (lists of items of the form <nodenum> or (not <nodenum>))
;; (defun make-context-array-from-array (dag-array-name dag-array dag-len tag-array2)
;;   (mv-let (predicate-nodenums context-indicator-list-array)
;;           (make-context-indicator-list-array dag-array-name dag-array dag-len tag-array2)
;;           (make-context-array-aux (+ -1 dag-len) context-indicator-list-array (make-empty-array 'context-array dag-len) predicate-nodenums 'context-array)))

;; (skip- proofs (verify-guards make-context-array-from-array))

;; ;returns a contextp
;; (defun get-context-for-nodenum.old (nodenum array-name array array-len tag-array2)
;;   (let* ((context-array (make-context-array-from-array array-name array array-len tag-array2))) ;fffixme overkill to compute anything below nodenum
;;     (aref1 'context-array context-array nodenum)))


;this was when i used the depth limit to abort a rewrite, but i don't use it anymore:
;;                            ;; If nothing changed we are done: - what if things just got reordered?  maybe that wont happen?
;;                            (if (equal new-dag-lst dag-lst)
;;                                new-dag-lst
;;                              ;; Otherwise, simplify again (BBBOZO no need, unless we hit the depth limit?):
;;                              (prog2$ (if (or (equal print :stable)
;;                                              (equal print t)
;;                                              (equal print :verbose))
;;                                          (print-list new-dag-lst)
;;                                        nil)
;;                                      (simplify-dag-lst new-dag-lst rule-alist slack-amount assumptions
;;                                                                     print-interval print interpreted-function-alist monitored-symbols)))))))))))






;(simplify-dag '((3 car 2) (2 cons 1 0) (1 quote 3) (0 . v)) (make-rules '(car-cons) state))

;;BOZO think about going top down and then bottom up...

;; (defun print-dag2-aux (dag-lst)
;;   (if (endp dag-lst)
;;       nil
;;     (print-dag2-aux (prog2$ (cw " ~x0~%" (car dag-lst))
;;                             (cdr dag-lst)))))

;; (skip- proofs (verify-guards print-dag2-aux))

;; (defun print-dag2 (dag-lst)
;;   (prog2$ (cw "The final dag:~%(")
;;           (prog2$ (print-dag2-aux dag-lst)
;;                   (cw ")~%"))))

;; (skip- proofs (verify-guards print-dag2))

;bozo move this stuff:

;; (DEFUN multi-union-eq (LST)
;;   (IF (ENDP LST)
;;       nil (union-eq (CAR LST) (multi-union-eq (CDR LST)))))

;; (defun aref1-lst (array-name array index-lst)
;;   (if (endp index-lst)
;;       nil
;;     (cons (aref1 array-name array (car index-lst))
;;           (aref1-lst array-name array (cdr index-lst)))))

;misspelled
;; (defun keep-integerps (items)
;;   (if (endp items)
;;       nil
;;       (if (integerp (car items))
;;           (cons (car items)
;;                 (keep-integerps (cdr items)))
;;           (keep-integerps (cdr items)))))

;; ;BOZO should use an array instead of an alist...
;; ;returns an alist that pairs each nodenum with a list of the variables it depends on
;; ;BOZO rewrite to avoid stackoverflows.. and perhaps use arrays for speed
;; (defun var-dependency-alist-aux (n len dag-array acc-array)
;;   (declare (xargs :measure (+ 1 (nfix (- len n)))
;;                   :verify-guards nil
;;                   ))
;;   (if (or (not (natp n))
;;           (not (natp len))
;;           (>= n len))
;;       acc-array
;;     (prog2$ (if (equal 0 (mod n 100)) (cw "Node number ~x0.~%" n) nil)
;;             (let ((expr (aref1 'dag-array dag-array n)))
;;               (if (variablep expr)
;;                   (var-dependency-alist-aux (+ 1 n)
;;                                             len
;;                                             dag-array
;;                                             (aset1-safe 'acc-array acc-array n (list expr))) ;one variable, namely expr itself
;;                 (if (fquotep expr)
;;                     (var-dependency-alist-aux (+ 1 n)
;;                                               len
;;                                               dag-array
;;                                               (aset1-safe 'acc-array acc-array n nil)) ;no variables
;;                   ;;function call:
;;                   (let* ( ;(fn (ffn-symb expr))
;;                          (args (fargs expr))
;;                          (arg-var-lists (aref1-lst 'acc-array acc-array (KEEP-INTEGERPS args)))
;;                          (args-vars (multi-union-eq arg-var-lists)))
;;                     (var-dependency-alist-aux (+ 1 n)
;;                                               len
;;                                               dag-array
;;                                               (aset1-safe 'acc-array acc-array n args-vars)))))))))

;; ;bozo printing may be slow
;; (defun var-dependency-alist (dag)
;;   (let* ((dag-array (make-into-array 'dag-array dag))
;;          (acc-array (make-empty-array 'acc-array (len dag)))
;;          (len (len dag)))
;;     ;bozo wrong?
;;     (array-to-alist (len dag) 'acc-array (var-dependency-alist-aux 0 len dag-array acc-array))))

;; (defun var-dependencies-for-node (nodenum dag)
;;   (let* ((dag-array (make-into-array 'dag-array dag))
;;          (acc-array (make-empty-array 'acc-array (len dag))))
;;     (aref1 'acc-array (var-dependency-alist-aux 0 (+ 1 nodenum) dag-array acc-array) nodenum)))

;; ;for each var, makes an expression looking it up in the alist and pairs the var with the nodenum of that expression
;; ;returns (mv variable-nodenum-alist-for-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;; (defun make-nodes-for-vars (vars alist-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc)
;;   (if (endp vars)
;;       (mv acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;     (let* ((var (car vars))
;;            (expr `(lookup-eq ',var ,alist-nodenum)))
;;       (mv-let (nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;               ;would like to simplify this right here..
;;               (add-function-call-expr-to-dag-array 'lookup-eq `(',var ,alist-nodenum)
;;                                                           dag-array dag-len dag-parent-array
;;                                                           dag-constant-alist dag-variable-alist)
;;               (make-nodes-for-vars (cdr vars)
;;                                    alist-nodenum
;;                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                    (acons var nodenum acc))))))

;; (skip- proofs (verify-guards make-nodes-for-vars))

;; ;this can blow up!
;; (defun pair-nodenums-with-terms (nodenums dag-lst)
;;   (if (endp nodenums)
;;       nil
;;     (let* ((nodenum (first nodenums))
;;            (term (dag-to-term-aux nodenum dag-lst)))
;;       (acons nodenum term (pair-nodenums-with-terms (cdr nodenums) dag-lst)))))

;; (skip- proofs (verify-guards pair-nodenums-with-terms))

;; ;this can blow up!
;; (defun pair-nodenums-with-terms-from-array (nodenums dag-array)
;;   (if (endp nodenums)
;;       nil
;;     (let* ((nodenum (first nodenums))
;;            (term (dag-to-term-aux-array nodenum dag-array)))
;;       (acons nodenum term (pair-nodenums-with-terms-from-array (cdr nodenums) dag-array)))))





;; ;returns (mv nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
;; ;the expr can't be a function applied to all constants
;; ;bozo make a separate version for each type (otherwise we redo the dispatch logic inside this routine)
;; ;now this refuses to add a node that's already present, even if dont-add-permanently is t (but what if we try to add the same node several times for relieve-hyp?)  we don't have a good way to pop off the parent info, etc. for the nodes added for relieve-hyp
;; (defun add-expr-to-dag-array (expr dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dont-add-permanently print-interval)
;; ;  (declare (ignore dont-add-permanently))
;;   (if (and (quotep expr)
;;            (or *store-constants-inline*
;;                (atom (unquote expr))
;;                (len-less-than 4 (unquote expr))) ;BOZO hope the atom test is okay...  well, really this changes how things work (ground terms look different now...)
;;            )
;;       (mv expr dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;     (if (variablep expr) ; BOZO this matches a nodenum too.  is that an error here?
;;         (let ((possible-index (lookup-eq expr dag-variable-alist))) ;BOZO use hashing?
;;           (if possible-index
;;               ;; if it's already present...
;;               (mv possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;             ;; otherwise, we add it...
;;             (mv dag-len ;BBOZO should we update this or not?
;;                 (aset1-safe 'dag-array dag-array dag-len expr)
;;                 (+ 1 dag-len)
;;                 dag-parent-array
;;                 dag-constant-alist
;;                 (if (not dont-add-permanently)
;;                     (acons expr dag-len dag-variable-alist)
;;                   dag-variable-alist))))
;;       (if (no-atoms (fargs expr)) ;; "constant" case
;;           (let ((possible-index (lookup-equal expr dag-constant-alist))) ;BOZO use hashing?
;;             (if possible-index
;;                 ;; if it's already present...
;;                 (mv possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;               ;; otherwise, we add it...
;;               (mv dag-len ;BBOZO should we update this or not?
;;                   (aset1-safe 'dag-array dag-array dag-len expr)
;;                   (+ 1 dag-len)
;;                   dag-parent-array
;;                   (if (not dont-add-permanently)
;;                       (acons expr dag-len dag-constant-alist)
;;                     dag-constant-alist)
;;                   dag-variable-alist)))
;;         ;; has at least one child that's a nodenum, so we can use the parent trick...
;;         ;; that is, to check the node's presence, compare it to the parents of one of its children
;;         (let ((possible-index
;;                (find-expr-using-parents expr dag-array dag-parent-array))) ;BOZO use hashing?
;;           (if possible-index ;is already present
;;               (mv possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;             ;; otherwise add it at the top
;;             (prog2$ (if (and print-interval
;;                              (equal 0 (mod dag-len print-interval)))
;; ;                          nil
;;                         (print-array2 'dag-array dag-array (+ -1 dag-len) ) ;
;; ;                          (cw "Adding node ~x0 to dag: ~x1.~%" dag-len (array-to-alist dag-len 'dag-array dag-array))

;;                       (if (and (not dont-add-permanently)
;;                                (equal 0 (mod dag-len 1000)))
;;                           (cw "Adding node ~x0.~%" dag-len)
;;                         nil))
;;                     (mv dag-len
;;                         (aset1-safe 'dag-array dag-array dag-len expr)
;;                         (+ 1 dag-len)
;;                         (if (not dont-add-permanently)
;;                             (add-to-parents-of-children expr dag-len dag-parent-array)
;;                           dag-parent-array)
;;                         dag-constant-alist
;;                         dag-variable-alist))))))))

;; (skip- proofs (verify-guards add-expr-to-dag-array))

;from the rewriter:

                          ;;               ;;Handle the various kinds of if:
                          ;;               ;;fffixme look up in assumptions now?
                          ;;               (mv-let (thenpart-or-elsepart ;if this is non-nil, we resolved the if test
                          ;;                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info)
                          ;;                       (if (or (eq 'if fn)
                          ;;                               (eq 'myif fn)
                          ;;                               (eq 'boolif fn)) ;BBOZO (what about bvif? - the test in a BVIF is a different arg) ;and? ;or?
                          ;;                           ;; TREE is an if (or related thing):
                          ;;                           (let ((test (farg1 tree))
                          ;;                                 (thenpart (farg2 tree))
                          ;;                                 (elsepart (farg3 tree)))
                          ;;                             ;; First, try to resolve the if-test:
                          ;;                             (mv-let (test-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info)
                          ;;                                     (simplify-tree-and-add-to-dag test
                          ;;                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          ;;                                                                   rule-alist
                          ;;                                                                   nil ;no trees are yet known equal to the test
                          ;;                                                                   assumptions equality-assumptions print-interval print memoization memoizep info interpreted-function-alist monitored-symbols embedded-dag-depth)
                          ;;                                     (if (quotep test-result)
                          ;;                                         ;; The test rewrote to a constant, so TREE is equal to its "then" branch or its "else" branch:
                          ;;                                         (mv (if (unquote test-result) thenpart elsepart)
                          ;;                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info)
                          ;;                                       ;; Otherwise, we couldn't resolve the test, so we will have to simplify both branches.
                          ;;                                       ;; I guess we rewrite the test again here, but the result should be memoized.
                          ;;                                       (mv nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info))))
                          ;;                         ;; it's not an ITE, so we didn't even attempt to resolve an IF test:
                          ;;                         (mv nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info))
                          ;;                       (if thenpart-or-elsepart
                          ;; ;fffffix need to add a boolfix if it's a boolif!
                          ;;                           (simplify-tree-and-add-to-dag thenpart-or-elsepart
                          ;;                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          ;;                                                         rule-alist
                          ;;                                                         (cons tree trees-equal-to-tree) ;we memoize tree as well
                          ;;                                                         assumptions equality-assumptions print-interval print memoization memoizep info interpreted-function-alist monitored-symbols embedded-dag-depth)

;; ;;; make a miter:
;; (defun make-miter-dag-aux (dag1 dag2)
;;   (declare (xargs :GUARD (and (ALIST-with-integer-keysp dag1)
;;                               (ALIST-with-integer-keysp dag2))
;;                   :guard-hints (("Goal" :in-theory (enable alistp-guard-hack ALIST-with-integer-keysp)))
;;                   :verify-guards nil
;;                   ))
;;   (mv-let (translation-alist new-dag)
;;           (merge-dags-allows-constants dag1 dag2)
;;           (let* ((dag2-nodenum (top-nodenum dag2))
;;                  (dag1-nodenum (lookup (top-nodenum dag1) translation-alist)))
;;             (mv-let (top-nodenum new-dag) ;will add-to-dag ever find this expression already present - almost certainly not?
;;                     (add-to-dag `(equal ,dag1-nodenum ,dag2-nodenum)
;;                                 new-dag)
;;                     (mv-let (top-nodenum new-dag) ;will add-to-dag ever find this expression already present - almost certainly not?
;;                             (add-to-dag `(not ,top-nodenum)
;;                                         new-dag)
;;                     (mv-let (top-nodenum new-dag) ;will add-to-dag ever find this expression already present - almost certainly not?
;;                             (add-to-dag `(bool-to-bit ,top-nodenum)
;;                                         new-dag)
;;                             (mv top-nodenum new-dag)))))))

;; (skip- proofs (verify-guards make-miter-dag-aux))

;; (defun make-miter-dag (dag1 dag2)
;;   (mv-let (node dag)
;;           (make-miter-dag-aux dag1 dag2)
;;           (declare (ignore node))
;;           dag))

;; (skip- proofs (verify-guards make-miter-dag))

;; ;a and b should have the same length
;; (defun zip-lists (a b)
;;   (if (endp a)
;;       nil
;;     (cons (car a) (cons (car b) (zip-lists (cdr a) (cdr b))))))

;; (defun quote-all (lst)
;;   (if (endp lst)
;;       nil
;;     (cons (list 'quote (car lst))
;;           (quote-all (cdr lst)))))

;; ;bozo compare to bvcat2 macro
;; ;bozo quotes the numbers..
;; (defun bvcat2-fn (params)
;;   (declare (xargs :guard (and params (true-listp params) (evenp (length params)))
;;                   :mode :program
;;                   ))
;;   (cond ((endp (cddr params))
;;          `(bvchop ;,(formal-+ -1 (car x))
;;            ',(car params)
;;            ,(cadr params)))
;;         ((endp (cddddr params))
;;          `(bvcat '1 ,(cadr params) '1 ,(cadddr params) ;,@params
;;                  ))
;;         (t
;;          `(bvcat ',(car params)
;;                  ,(cadr params)
;;                  ',(bvcat-size (cddr params))
;;                  ,(bvcat2-fn (cddr params))))))

;; (defun bvcat2-vars-fn (base-symbol varsize first-num last-num)
;;   (declare (xargs :mode :program))
;;   (let* ((direction (if (< last-num first-num) :down :up))
;;          (low-num (min first-num last-num))
;;          (high-num (max first-num last-num))
;;          (numvars (+ 1 (- high-num low-num)))
;;          (varnames (make-var-names-aux base-symbol low-num high-num))
;;          (varnames (if (equal direction :down)
;;                        (reverse-list varnames)
;;                      varnames))
;; ;         (varnames (quote-all varnames))
;;          (sizes (repeat numvars varsize))
;;          (bvcat2-args (zip-lists sizes varnames)))
;;     (bvcat2-fn bvcat2-args)))

;; (defmacro bvcat2-vars (base-symbol varsize first-num last-num)
;;   (bvcat2-vars-fn base-symbol varsize first-num last-num))

;todo: add support for polarity - what if a node occurs with both polarities?
;todo: gather up all rules used and report at the end?
;todo: don't count rules used in failed attempts to relieve hyps?

; what should the waterfall look like?
; dag prover tactics:
; repeatedly simplify literals
; elim - one or all?
; subst for var(s) - do better?
; sat - including calling stp and my homegrown one (for things like all-unsigned-byte-p, true-listp, and len)?
; partition literals - do very early on and keep rechecking?



;;management of dag-runes (for calling the dag prover from the top level):


;turn ifs into myifs?


;; ;decides whether nodenum-or-quotep is simpler than nodenum2
;; ;fffixme computing this over and over might be very expensive - better to precompute the sizes?
;; (defun simpler-dag-termp (nodenum-or-quotep nodenum2 dag-array)
;;   (if (quotep nodenum-or-quotep)
;;       t
;;     (let* ((max-nodenum (max nodenum-or-quotep nodenum2))
;;            (node-count (+ 1 max-nodenum))
;;            (node-size-array (make-empty-array 'node-size-array node-count))
;;            (node-size-array (build-size-array-for-nodes (list nodenum-or-quotep nodenum2) 'dag-array dag-array 'node-size-array node-size-array))
;; ;;           (node-size-array (compute-dag-array-size-aux 0 node-count 'dag-array dag-array 'node-size-array node-size-array)))
;;            (size1 (aref1 'node-size-array node-size-array nodenum-or-quotep))
;;            (size2 (aref1 'node-size-array node-size-array nodenum2)))
;;       (if (< size1 size2)
;;           t
;;         (if (< size2 size1)
;;             nil
;;           ;;we break ties in size by comparing nodenums:
;;           ;;fixme could this lead to loops?
;;           (< nodenum-or-quotep nodenum2))))))

;; (skip- proofs (verify-guards simpler-dag-termp))

;; ;decides whether nodenum-or-quotep is simpler than nodenum2
;; ;fffixme computing this over and over might be very expensive - better to precompute the sizes?
;; (defun simpler-dag-termp2 (nodenum term dag-array)
;;   (let* ((node-count (+ 1 nodenum))
;;          (node-size-array (make-empty-array 'node-size-array node-count))
;;          (node-size-array (compute-dag-array-size-aux 0 node-count 'dag-array dag-array 'node-size-array node-size-array))
;;          (size (aref1 'node-size-array node-size-array nodenum))
;;          (term-size (
;;          )
;;     (if (< size1 size2)
;;         t
;;       (if (< size2 size1)
;;           nil
;;         ;;we break ties in size by comparing nodenums:
;;         (< nodenum-or-quotep nodenum2)))))

;; (skip- proofs (verify-guards simpler-dag-termp2))

;; Tries to replace NODENUM (current only with a constant) using facts known
;; from the NODENUMS-TO-ASSUME-FALSE.  The result is related to NODENUM by the
;; EQUIV passed in ('equal or 'iff).
;; Returns a quotep, or nil to indicate failure.  May some day be allowed to return a nodenum.
;; TODO: To speed this up, we could separately track nodenums to assume false and nodenums to assume true (non-nil).
;; TODO: To speed this up, we could perhaps index the known true/false facts by top function-symbol.
;; TODO: To speed this up, we could perhaps maintain this information as node-replacement pairs, perhaps even in an array.
;; If there are multiple matches, the first one will fire, even if later ones might be better.
(defund replace-nodenum-using-assumptions-for-axe-prover (nodenum
                                                          equiv ;todo: perhaps pass in an iff-flag
                                                          nodenums-to-assume-false dag-array
                                                          ;;print
                                                          )
  (declare (xargs :guard (and (natp nodenum)
                              (symbolp equiv)
                              (all-natp nodenums-to-assume-false)
                              (true-listp nodenums-to-assume-false)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem (cons nodenum nodenums-to-assume-false)))))
                  :guard-hints (("Goal"
                                 :use ((:instance true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
                                                  (dag-array-name 'dag-array)
                                                  (n (nth 0 nodenums-to-assume-false)))
                                       (:instance true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
                                                  (dag-array-name 'dag-array)
                                                  (n (nth 0 (dargs (aref1 'dag-array dag-array (nth 0 nodenums-to-assume-false)))))))
                                 :in-theory (e/d (car-becomes-nth-of-0
                                                  NATP-OF-+-OF-1)
                                                 (natp
                                                  true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp
                                                  true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple))))))
  (if (endp nodenums-to-assume-false)
      nil ;; failure to rewrite NODENUM
    (let* ((nodenum-to-assume-false (first nodenums-to-assume-false)))
      (if (eql nodenum nodenum-to-assume-false) ; could do (member nodenum nodenums-to-assume-false) in a wrapper function
          ;; NODENUM is among the NODENUMS-TO-ASSUME-FALSE, so we replace it with 'nil:
          *nil*
        (let* ((expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false)))
          (if (not (and (call-of 'not expr-to-assume-false)
                        (consp (dargs expr-to-assume-false))
                        ;; (not (consp (rest (dargs expr-to-assume-false)))) ;todo: think about bad arities
                        (atom (darg1 expr-to-assume-false)) ;makes sure it's a nodenum
                        ))
              ;; expr-to-assume-false does not have a form we can use, so keep looking:
              (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv (rest nodenums-to-assume-false) dag-array
                                                                ;;print
                                                                )
            ;; EXPR-TO-ASSUME-FALSE is of the form (not <nodenum-to-assume-non-nil>):
            (let ((nodenum-to-assume-non-nil (darg1 expr-to-assume-false)))
              (if (and (eq 'iff equiv) ;fixme equivs may someday not be comparable using eq
                       (eql nodenum nodenum-to-assume-non-nil))
                  ;; NODENUM is equal to NODENUM-TO-ASSUME-NON-NIL, and since
                  ;; we only must preserve IFF, we can replace it with 't:
                  ;; TODO: If nodenum is the nodenum of a boolean (either
                  ;; because of the ffn-symb or because we have a hyp to that
                  ;; effect), we could replace it with *t* even if the equiv is
                  ;; 'equal:
                  *t*
                (let ((expr-to-assume-non-nil (aref1 'dag-array dag-array nodenum-to-assume-non-nil)))
                  (if (not (and (call-of 'equal expr-to-assume-non-nil)
                                ;;(= 2 (len (dargs expr-to-assume-non-nil)))
                                (consp (rest (dargs expr-to-assume-non-nil))) ;todo: think about bad arities
                                ))
                      ;; expr-to-assume-non-nil does not have a form we can use, so keep looking:
                      (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv (rest nodenums-to-assume-false) dag-array
                                                                        ;;print
                                                                        )
                    (let ((darg1 (darg1 expr-to-assume-non-nil))
                          (darg2 (darg2 expr-to-assume-non-nil)))
                      (if (and (eql nodenum darg2)
                               ;; expr-to-assume-non-nil is of the form (equal <thing> NODENUM):
                               ;; note the order: equalities fire right-to-left, since the small thing is put first
                               (consp darg1) ;; check for quotep
                               ;; (if (quotep darg1)
                               ;;     t ;always put a constant in
                               ;;   ;;thing is a nodenum:
                               ;;   nil ;Sun May 15 18:35:43 2011
                               ;;   ;; (if (variablep (aref1 'dag-array dag-array thing))
                               ;;   ;;     nil ;don't put a variable back in... (or can we order the variables???)
                               ;;   ;;   (or nil ;(simpler-dag-termp thing nodenum dag-array) ;fixme do we always want to do this?  fixme is this known from how the equality is ordered? ;can this loop?
                               ;;   ;;       (and (variablep (aref1 'dag-array dag-array nodenum)) ;don't test this over and over?  or we could wait until substitute-a-var?
                               ;;   ;;            (not (member nodenum (supporters-of-node thing 'dag-array dag-array 'tag-array-for-supporters))))
                               ;;   ;;       ))
                               ;;   )
                               ) ;expensive?!
                          ;; ffixme, don't do this when the assumptions haven't yet been simplified? can lead to loops!
                          (progn$ ;; (and (eq :verbose print) (cw "Putting in ~x0 for node ~x1.~%" (darg1 expr-to-assume-non-nil) nodenum))
                           darg1)
                        ;;this whole case is new (FFIXME this violates the rule about equalities firing from right to left):
                        ;;fixme keep this in sync with the stuff above...
                        (if (and (eql nodenum darg1)
                                 (consp darg2) ;; check for quotep
                                 ;; ;; expr-to-assume-non-nil is of the form (equal NODENUM <thing>):
                                 ;; (let ((thing (darg2 expr-to-assume-non-nil)))
                                 ;;   (if (quotep thing)
                                 ;;       t ;always put a quotep in
                                 ;;     nil ;Sun May 15 18:35:52 2011
                                 ;;     ;; (if (variablep (aref1 'dag-array dag-array thing))
                                 ;;     ;;     nil ;don't put a variable back in...
                                 ;;     ;;   (or nil ;(simpler-dag-termp thing nodenum dag-array)
                                 ;;     ;;       (and (variablep (aref1 'dag-array dag-array nodenum))
                                 ;;     ;;            (not (member nodenum (supporters-of-node thing 'dag-array dag-array 'tag-array-for-supporters))))))
                                 ;;     ))
                                 )
                            ;; ffixme, don't do this when the assumptions haven't yet been simplified? can lead to loops!
                            (progn$ ;; (and (eq :verbose print) (cw "Putting in ~x0 for node ~x1.~%" (darg2 expr-to-assume-non-nil) nodenum))
                             darg2)
                          ;; keep looking:
                          (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv (rest nodenums-to-assume-false) dag-array
                                                                            ;;print
                                                                            ))))))))))))))

;; Currently it can only put in a quotep!
(defthm myquotep-of-replace-nodenum-using-assumptions-for-axe-prover
  (implies (and (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)
                (natp nodenum)
                ;;(symbolp equiv)
                (all-natp nodenums-to-assume-false)
                ;;(true-listp nodenums-to-assume-false)
                (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem (cons nodenum nodenums-to-assume-false)))))
           (myquotep (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array)))
  :hints (("Goal"
           :in-theory (e/d (replace-nodenum-using-assumptions-for-axe-prover
                            car-becomes-nth-of-0
                            NATP-OF-+-OF-1)
                           (natp
                            ;;quotep
                            myquotep
                            ;;MAXELEM-OF-CONS
                            )))))

;x must be a nodenum or quotep:
(defmacro isnodenum (x) `(not (consp ,x))) ;fixme would (atom be faster?)
;x must be a nodenum or quotep:
(defmacro isconstant (x) `(consp ,x))

(defthm not-<-of-nth-when-all-natp
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (all-natp x))
           (not (< (nth n x) k)))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

;can we deprecate this?  or split for var terms and all others - could just add term to the dag and use the main routine
;do we need both this and the version for a nodenum?
;"term" is either a variable or a function applied to a list of constants and nodenums
;looks for a nodenum-to-assume-false that points to:
; term -- rewrite term to false
; (not term) -- rewrite term to t, if term is a call of a known-predicate (fixme we could try to prove that it's a boolean - what if we have that as a hyp?)
; (not (equal new-nodenum-or-quotep term)) - rewrite term to the new term
;fixme more generally, if we have a hyp of (booleanp term) we can safely rewrite term in an iff context everywhere?
;equiv is 'equal or 'iff (or nil, which means equal) for now
;; Returns a nodenum or quotep, or nil to indicate failure.
;ffixme this should not fail if it's trying to use an equality we've already decided to substitute and drop..
;perhaps term is always either a var of a fn-call applied to nodenums and quoteps
;todo: rename term to tree in the param and this function's name:
(defund replace-term-using-assumptions-for-axe-prover (term equiv nodenums-to-assume-false dag-array print)
  (declare (xargs :guard (and (axe-treep term)
                              (symbolp equiv)
                              (all-natp nodenums-to-assume-false)
                              (true-listp nodenums-to-assume-false)
                              (if (consp nodenums-to-assume-false)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false)))
                                t))
                  :guard-hints (("Goal" :in-theory (e/d (CAR-BECOMES-NTH-OF-0) (natp))))))
  (if (endp nodenums-to-assume-false)
      nil ;; failed to rewrite TERM
    (let* ((nodenum-to-assume-false (first nodenums-to-assume-false))
           (expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false)))
      (if (equal term expr-to-assume-false)
          *nil* ; TERM can be safely assumed false
        (if (not (and (call-of 'not expr-to-assume-false)
                      (= 1 (len (dargs expr-to-assume-false)))
                      (isnodenum (darg1 expr-to-assume-false))))
            (replace-term-using-assumptions-for-axe-prover term equiv (rest nodenums-to-assume-false) dag-array print)
          ;; EXPR-TO-ASSUME-FALSE is of the form (not <nodenum>):
          (let ((non-nil-expr (aref1 'dag-array dag-array (darg1 expr-to-assume-false))))
            (if (and (eq equiv 'iff)
                     (equal term non-nil-expr) ;fffixme allow the equal to be weaker?  huh?
;                     (consp term) ;fixme move up so we don't retest this?
;                    (member-eq (ffn-symb term) *known-predicates-jvm*) ;move up?
;fixme what if we have a hyp that says that term is a boolean?
                     )
                *t* ;since it's assumed non-nil and we only have to preserve iff, it's t
              (if (not (and (call-of 'equal non-nil-expr)
                            (= 2 (len (dargs non-nil-expr)))
                            (isnodenum (darg2 non-nil-expr))))
                  (replace-term-using-assumptions-for-axe-prover term equiv (rest nodenums-to-assume-false) dag-array print)
                ;; this is consistent with what we've been doing all along (turning equalities around to bring the smaller term to the left)
                (if (and (equal term (aref1 'dag-array dag-array (darg2 non-nil-expr))) ;fixme allow the equal to be weaker?
                         ;; NON-NIL-EXPR is of the form (equal <thing> <nodenum-of-term>)
                         ;;recall that equalities now rewrite the term on the right to the term on the left (the smaller term)

                         ;;(quotep (darg1 non-nil-expr))  ;;new! ;Sun Feb 14 12:33:01 2010 ;fffixme allow vars?  keep this in sync with the code that decides whether to substitute?
                         ;;fixme maybe the protection against looping should go right here?
                         ;; how should we prevent loops?  what if we have (equal <x> <y>) <x> would rewriter back to <y> in the context in which <y> appears?
;new Mon Mar 29 09:48:23 2010:
                         (if (quotep (darg1 non-nil-expr))
                             t ;always put a quotep in
                           nil ;Sun May 15 21:49:00 2011
                           ;;                            (if (variablep (aref1 'dag-array dag-array (darg1 non-nil-expr)))
                           ;;                                nil ;don't put a variable back in
                           ;;                              (variablep term) ;nil ;Wed Mar 31 08:32:09 2010  ;fixme wait until substitute-a-var?  can this loop if term (a variable) is equated to something invcluding itself?
                           ;; ;;                              (or (simpler-dag-termp2 (darg1 non-nil-expr) term dag-array) ;fffixme gotta fix this up to take a term
                           ;; ;;                                  (and (variablep term)
                           ;; ;;                                       (not (member nodenum ;fffixme gotta fix this up to take a term
                           ;; ;;                                                    (supporters-of-node (darg1 non-nil-expr) 'dag-array dag-array 'tag-array-for-supporters)))))
                           ;;                              )
                           ))
                    (prog2$ (and (eq :verbose print)
                                 (cw "Putting in ~x0 for term ~x1.~%" (darg1 non-nil-expr) term))
                            (darg1 non-nil-expr))
                  (replace-term-using-assumptions-for-axe-prover term equiv (rest nodenums-to-assume-false) dag-array print))))))))))

(defthm replace-term-using-assumptions-for-axe-prover-forward-to-consp
  (implies (replace-term-using-assumptions-for-axe-prover term equiv nodenums-to-assume-false dag-array print)
           (consp nodenums-to-assume-false))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable replace-term-using-assumptions-for-axe-prover))))

;todo: on fact, it's always a quotep !
;; (defthm dargp-of-replace-term-using-assumptions-for-axe-prover
;;   (implies (and (replace-term-using-assumptions-for-axe-prover term equiv nodenums-to-assume-false dag-array print)
;;                 (axe-treep term)
;;                 (symbolp equiv)
;;                 (all-natp nodenums-to-assume-false)
;;                 (true-listp nodenums-to-assume-false)
;;                 ;; (if (consp nodenums-to-assume-false)
;;                 ;;     (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (maxelem nodenums-to-assume-false)))
;;                 ;;   t)
;;                 )
;;            (dargp (replace-term-using-assumptions-for-axe-prover term equiv nodenums-to-assume-false dag-array print)))
;;   :hints (("Goal" :in-theory (e/d (replace-term-using-assumptions-for-axe-prover) (dargp)))))

;; hyp is a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars
;; returns (mv success-flg alist-for-free-vars)
;; if success-flg is nil, the alist returned is irrelevant
;; the alist returned maps variables to nodenums or quoteps
(defun match-hyp-with-nodenum-to-assume-false (hyp nodenum-to-assume-false dag-array dag-len)
   (declare (xargs :guard (and (axe-treep hyp)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (natp nodenum-to-assume-false)
                               (< nodenum-to-assume-false dag-len))
                   :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))
            (ignore dag-len) ;todo
            )
  ;; if hyp is of the form (not <x>) then try to match <x> with the nodenum-to-assume-false
  ;;ffixme what if hyp is of the form (equal .. nil) or (equal nil ..)?
   (if (and (call-of 'not hyp)
            (= 1 (len (fargs hyp))))
      (unify-tree-with-dag-node (farg1 hyp) nodenum-to-assume-false dag-array nil)
    ;;otherwise we require the expr assumed false to be a call of NOT
    (let ((expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false))) ;could do this at a shallower level?
      (if (and (call-of 'not expr-to-assume-false)
               (= 1 (len (dargs expr-to-assume-false))))
          (let ((arg (darg1 expr-to-assume-false)))
            (if (consp arg) ;whoa, it's a constant!
                (mv nil nil)
              (unify-tree-with-dag-node hyp arg dag-array nil)))
        (mv nil nil)))))

;; ;returns (mv success-flg alist-for-free-vars)
;; ;; the alist returned maps variables to nodenums or quoteps
;; ;;fixme - faster to extend the alist? maybe not, since we'd be checking a longer alist when doing the matching?
;; ;;fixme - handle assumptions of the forms foo and (equal foo 't) in the same way?
;; ;; hyp is a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars
;; ;; if success-flg is nil, the alist returned is irrelevant
;; ;could we use just 1 return value (nil would mean failure)?
;; (defun match-hyp-in-nodenums-to-assume-false (hyp nodenums-to-assume-false dag-array)
;;   (if (endp nodenums-to-assume-false)
;;       (mv nil nil)
;;     (mv-let (matchp alist)
;;             (match-hyp-with-nodenum-to-assume-false hyp (first nodenums-to-assume-false) dag-array)
;;             (if matchp
;;                 (mv t alist)
;;               (match-hyp-in-nodenums-to-assume-false hyp (rest nodenums-to-assume-false) dag-array)))))

;; (skip -proofs (verify-guards match-hyp-in-nodenums-to-assume-false))

;; ;don't lookup any indices that are quoteps
;; ;is this just a fixup function?
;; (defun lookup-non-quoteps (array-name array indices)
;;   (declare (xargs :guard (and (array1p array-name array)
;;                               (true-listp indices)
;;                               (all-dargp-less-than indices (alen1 array-name array)))))
;;   (if (endp indices)
;;       nil
;;     (let ((index (car indices)))
;;       (cons (if (consp index) ;check for quotep
;;                 index
;;               (aref1 array-name array index))
;;             (lookup-non-quoteps array-name array (cdr indices))))))

;; ;; Keep the args that are nodenums and that correspond to nil in merge-dag-array.
;; (defun get-args-to-merge (args array)
;;   (declare (xargs :guard (and (true-listp args)
;;                               (all-dargp args)
;;                               (array1p 'merge-dag-array array)
;;                               (< (largest-non-quotep args) (alen1 'merge-dag-array array)))))
;;   (if (endp args)
;;       nil
;;     (let ((arg (car args)))
;;       (if (consp arg) ;skip quoted constants
;;           (get-args-to-merge (cdr args) array)
;;         (if (aref1 'merge-dag-array array arg)
;;             (get-args-to-merge (cdr args) array)
;;           (cons arg (get-args-to-merge (cdr args) array)))))))

;; (defun lookup-args-in-merge-dag-array (args array)
;;   (declare (xargs :guard (and (true-listp args)
;;                               (all-dargp args)
;;                               (array1p 'merge-dag-array array)
;;                               (< (largest-non-quotep args) (alen1 'merge-dag-array array)))))
;;   (if (endp args)
;;       nil
;;     (let ((arg (car args)))
;;       (if (quotep arg)
;;           (cons arg
;;                 (lookup-args-in-merge-dag-array (cdr args) array))
;;         (cons (aref1 'merge-dag-array array arg)
;;               (lookup-args-in-merge-dag-array (cdr args) array))))))

;example justification:
;; (thm
;;  (implies (iff y1 y2)
;;           (equal (iff x y1)
;;                  (iff x y2))))

(defun all-symbol-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (symbol-alistp (first x))
         (all-symbol-alistp (rest x)))))

(defthm symbol-alistp-of-lookup-equal-when-all-symbol-alistp-of-strip-cdrs
  (implies (all-symbol-alistp (strip-cdrs alist))
           (symbol-alistp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable all-symbol-alistp lookup-equal assoc-equal))))

;; equiv-alist maps equivs to alists from function names to the equiv-lists to maintain for their args
(defun get-equivs (equiv fn equiv-alist)
  (declare (xargs :guard (and (symbol-alistp equiv-alist)
                              (all-symbol-alistp (strip-cdrs equiv-alist)))))
  (lookup-eq fn (lookup-eq equiv equiv-alist)))

;in this table, you look up the equivalence to preserve and the function being rewritten, and you get the list of equivalences to use for the function's arguments
(defconst *congruence-table*
  ;;fixme
  ;;justify these by proving congruences?
  (acons 'iff
         (acons 'iff '(iff iff)
                (acons 'bvif '(equal iff equal equal)
;this means if we are trying to preserve iff, and we are rewriting a boolor, use iff and iff for the args:
                       (acons 'boolor '(iff iff)
                              (acons 'boolxor '(iff iff)
                                     (acons 'boolif '(iff iff iff)
                                            (acons 'booland '(iff iff)
                                                   (acons 'not '(iff)
                                                          nil)))))))
         (acons 'equal
                (acons 'bool-to-bit '(iff) ;new
                       (acons 'iff '(iff iff)
                              (acons 'bvif '(equal iff equal equal)
                                     (acons 'boolor '(iff iff)
                                            (acons 'boolxor '(iff iff)
                                                   (acons 'boolif '(iff iff iff)
                                                          (acons 'booland '(iff iff)
                                                                 (acons 'not '(iff)
                                                                        nil))))))))
                nil)))

;Returns (mv erp disjuncts dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;where DISJUNCTS is a set of nodenums whose disjunction is equivalent (iff? could we just say implies?) to either (or nodenum acc), if negated-flg is nil, or to (or (not nodenum) acc), if negated-flg is non-nil
; and the dag may have been extended (could we say they just imply it?)
;fixme could this be expensive if there is a lot of shared structure?
;note: some of the disjuncts may not exist in the dag (ex: for (not (booland x y)), the disjuncts are (not x) and (not y), and these may not exist in the dag).  thus, this returns a possibly-extended dag.
;ffixme handle non-predicates (in which case we'll have an if nest, not a boolor nest)?
(defund get-disjuncts (nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (natp nodenum)
                              (< nodenum dag-len)
                              (nat-listp acc))
                  :measure (nfix nodenum)
                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :verify-guards nil ; done below
                  ))
  (if (or (quotep nodenum)
          (not (mbt (natp nodenum)))
          (not (mbt (< nodenum dag-len)))
          (not (mbt (pseudo-dag-arrayp 'dag-array dag-array dag-len))))
      ;;(cons nodenum acc) ;fffffixme this shouldn't happen...
      (mv (erp-t)
          (prog2$ (hard-error 'get-disjuncts "Should not have a constant here but we have ~x0 (make sure boolor/booland/etc of constant rules are on)" (acons #\0 nodenum nil))
                  nil ;what should we have here?
                  )
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (if (not negated-flg)
        (let ((expr (aref1 'dag-array dag-array nodenum)))
          (if (and (call-of 'boolor expr)
                   (= 2 (len (dargs expr)))
                   (not (consp (darg1 expr))) ;handle this case?
                   (not (consp (darg2 expr))) ;handle this case?
                   (mbt (< (darg1 expr) nodenum))
                   (mbt (< (darg2 expr) nodenum))
                   )
              ;; it is a boolor, so get disjuncts from the arguments:
              (mv-let (erp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (get-disjuncts (darg2 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                               nil) ;negated-flg
                (if erp
                    (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                  (get-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 acc
                                 nil))) ;negated-flg
            (if (and (call-of 'not expr)
                     (= 1 (len (dargs expr)))
                     (not (consp (darg1 expr))) ;handle this case?
                     (mbt (< (darg1 expr) nodenum)))
                ;;it's a call of not, so recur and set negated-flg to t
                (get-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                               t) ;;negated-flg
              ;;it's not something we know how to get disjuncts from:
              (mv (erp-nil)
                  (add-to-set-eql nodenum acc)
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
      ;;negated-flg case:
      (let ((expr (aref1 'dag-array dag-array nodenum)))
        (if (and (call-of 'booland expr)
                 (= 2 (len (dargs expr)))
                 (not (consp (darg1 expr))) ;handle this case?
                 (not (consp (darg2 expr))) ;handle this case?
                 (mbt (< (darg1 expr) nodenum))
                 (mbt (< (darg2 expr) nodenum)))
            ;; it is a negated call to booland, so get disjuncts from the arguments and negate them:
            ;; note that (not (booland x y)) = (boolor (not x) (not y))
            (mv-let (erp acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (get-disjuncts (darg2 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                             t) ;negated-flg
              (if erp
                  (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (get-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                               acc
                               t))) ;negated-flg
          (if (and (call-of 'not expr)
                   (= 1 (len (dargs expr)))
                   (not (consp (darg1 expr))) ;handle this case?
                   (mbt (< (darg1 expr) nodenum)))
              ;;it's a negated call of not, so recur and set negated-flg to nil
              ;; note that (not (not x)) iff x (fixme do we need to call bool-fix$inline - probably not?)?
              (get-disjuncts (darg1 expr) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc
                             nil) ;;negated-flg
            ;;it's not something we know how to get disjuncts from, so add its negation and return the nodenum:
            (mv-let (erp negated-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (add-function-call-expr-to-dag-array 'not (list nodenum) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (mv erp
                  (add-to-set-eql negated-nodenum acc) ;meaningless if erp is t.
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))))

(in-theory (disable add-to-set-equal)) ;move

(def-dag-builder-theorems
  (get-disjuncts nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg)
  (mv erp disjuncts dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))

(defthm nat-listp-of-mv-nth-1-of-get-disjuncts
  (implies  (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                 (natp nodenum)
                 (< nodenum dag-len)
                 (nat-listp acc))
            (nat-listp (mv-nth 1 (get-disjuncts nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist acc negated-flg))))
  :hints (("Goal" :in-theory (e/d (get-disjuncts) (natp)))))

(verify-guards get-disjuncts :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) (natp)))))

;can be used to test get-disjuncts:
;; (defun get-disjuncts-of-term (term)
;;   (let* ((dag-lst (dagify-term term))
;;          (dag-len (len dag-lst))
;;          (dag-array (MAKE-INTO-ARRAY 'dag-array dag-lst)))
;;     (mv-let (dag-parent-array dag-constant-alist dag-variable-alist)
;;             (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len)
;;             (mv-let (disjuncts dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                     (get-disjuncts (+ -1 dag-len) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nil nil)
;;                     (declare (ignore dag-len dag-parent-array dag-constant-alist dag-variable-alist))
;;                     (list disjuncts dag-array)))))
;; ex: (GET-DISJUNCTS-OF-TERM '(boolor w (not (booland x (not (boolor y z))))))


;; ;; This one does no simplification (e.g., when we are rewriting a hide)
;; Does it basically just inline constants?
;; (skip -proofs
;;  ;; returns (mv erp merge-dag-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;  ;; merge-dag-array tracks the nodenum or quote that each node rewrote to
;;  (defun merge-supporting-nodes-into-dag (worklist merge-dag-array
;;                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;    (if (endp worklist)
;;        (mv (erp-nil) merge-dag-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;      (let* ((nodenum (car worklist)))
;;        (if (aref1 'merge-dag-array merge-dag-array nodenum)
;;            (merge-supporting-nodes-into-dag (cdr worklist) merge-dag-array
;;                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;          (let ((expr (aref1 'dag-array dag-array nodenum)))
;;            (if (atom expr) ;must be a variable
;;                (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                  (add-variable-to-dag-array
;;                   expr dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                  (if erp
;;                      (mv erp merge-dag-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                    (merge-supporting-nodes-into-dag (cdr worklist)
;;                                                     (aset1-safe 'merge-dag-array merge-dag-array nodenum new-nodenum)
;;                                                     dag-array dag-len dag-parent-array
;;                                                     dag-constant-alist dag-variable-alist)))
;;              (let ((fn (ffn-symb expr)))
;;                (if (eq 'quote fn)
;;                    (merge-supporting-nodes-into-dag (cdr worklist)
;;                                                     (aset1-safe 'merge-dag-array merge-dag-array nodenum expr)
;;                                                     dag-array dag-len dag-parent-array
;;                                                     dag-constant-alist dag-variable-alist)
;;                  ;;regular function call:
;;                  ;;first make sure that the args have been processed
;;                  (let* ((args (dargs expr))
;;                         (args-to-merge (get-args-to-merge args merge-dag-array)))
;;                    (if args-to-merge
;;                        (merge-supporting-nodes-into-dag (append args-to-merge worklist)
;;                                                         merge-dag-array
;;                                                         dag-array dag-len dag-parent-array
;;                                                         dag-constant-alist dag-variable-alist)
;;                      ;;all args are merged:
;;                      (let* ((args (lookup-args-in-merge-dag-array args merge-dag-array)))
;;                        (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                          (add-function-call-expr-to-dag-array
;;                           fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                          (if erp
;;                              (mv erp merge-dag-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                            (merge-supporting-nodes-into-dag (cdr worklist)
;;                                                             (aset1-safe 'merge-dag-array merge-dag-array nodenum new-nodenum)
;;                                                             dag-array dag-len dag-parent-array
;;                                                             dag-constant-alist dag-variable-alist)))))))))))))))

;;(skip -proofs (verify-guards merge-supporting-nodes-into-dag))

(defthm car-of-dargs-becomes-nth-of-0
  (equal (car (dargs expr))
         (nth 0 (dargs expr))))

(defthm cadr-of-dargs-becomes-nth-of-1
  (equal (cadr (dargs expr))
         (nth 1 (dargs expr))))

(defund get-var-length-alist-for-tuple-elimination (nodenums-to-assume-false dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (true-listp nodenums-to-assume-false)
                              (all-natp nodenums-to-assume-false)
                              (all-< nodenums-to-assume-false dag-len))
                  :guard-hints (("Goal" :in-theory (e/d () (PSEUDO-DAG-ARRAYP))))))
  (if (endp nodenums-to-assume-false)
      acc
    (let* ((nodenum (first nodenums-to-assume-false))
           (not-expr (aref1 'dag-array dag-array nodenum))
           (acc (if (and (consp not-expr)
                         (eq 'not (ffn-symb not-expr))
                         (= 1 (len (dargs not-expr)))
                         (not (consp (darg1 not-expr))))
                    (let ((expr (aref1 'dag-array dag-array (darg1 not-expr))))
                      (if (and (call-of 'equal expr)
                               (= 2 (len (dargs expr)))
                               (quotep (darg1 expr))
                               ;;allow 0?:
                               (posp (unquote (darg1 expr)))
                               (< (unquote (darg1 expr)) 50) ;fffixme had 40, but that was too small for the cbc proof (think more about this..)
                               (not (consp (darg2 expr)))
                               )
                          (let ((possible-len-of-var (aref1 'dag-array dag-array (darg2 expr))))
                            (if (and (consp possible-len-of-var)
                                     (eq 'len (ffn-symb possible-len-of-var))
                                     (= 1 (len (dargs possible-len-of-var)))
                                     (not (consp (darg1 possible-len-of-var))))
                                (let ((possible-var (aref1 'dag-array dag-array (darg1 possible-len-of-var))))
                                  (if (symbolp possible-var)
                                      (acons-fast possible-var (unquote (darg1 expr)) acc)
                                    acc))
                              acc))
                        acc))
                  acc)))
      (get-var-length-alist-for-tuple-elimination (cdr nodenums-to-assume-false) dag-array dag-len acc))))

(defthm symbol-alistp-of-get-var-length-alist-for-tuple-elimination
  (equal (symbol-alistp (get-var-length-alist-for-tuple-elimination nodenums-to-assume-false dag-array dag-len acc))
         (symbol-alistp acc))
  :hints (("Goal" :in-theory (enable get-var-length-alist-for-tuple-elimination))))

(defthm symbol-alistp-of-get-var-length-alist-for-tuple-elimination-type
  (implies (symbol-alistp acc)
           (symbol-alistp (get-var-length-alist-for-tuple-elimination nodenums-to-assume-false dag-array dag-len acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable get-var-length-alist-for-tuple-elimination))))

(defthm acl2-number-of-lookup-equal-when-all-natp-of-strip-cdrs
  (implies (all-natp (strip-cdrs acc))
           (iff (acl2-numberp (lookup-equal var acc))
                (member-equal var (strip-cars acc))))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal strip-cars member-equal))))

(defthm acl2-numberp-of-lookup-equal-of-get-var-length-alist-for-tuple-elimination
  (implies (all-natp (strip-cdrs acc))
           (iff (acl2-numberp (lookup-equal var (get-var-length-alist-for-tuple-elimination literal-nodenums dag-array dag-len acc)))
                (member-equal var (strip-cars (get-var-length-alist-for-tuple-elimination literal-nodenums dag-array dag-len acc)))))
  :hints (("Goal" :in-theory (enable get-var-length-alist-for-tuple-elimination))))

;explores worklist and all supporting nodes
;any node that is a parent of NODENUM and whose fn is not among FNS causes this to return nil
;fixme stop once we hit a nodenum smaller than NODENUM?
(defun nodenum-only-appears-in (worklist dag-array dag-len nodenum fns done-array)
  (declare (xargs ;; The measure is, first the number of unhandled nodes, then, if unchanged, check the length of the worklist.
            :measure (make-ord 1
                               (+ 1 ;coeff must be positive
                                  (if (not (natp (alen1 'done-array done-array)))
                                      0
                                    (+ 1 (- (alen1 'done-array done-array)
                                            (num-handled-nodes 'done-array done-array)))))
                               (len worklist))
            :guard (and (nat-listp worklist)
                        (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                        (array1p 'done-array done-array)
                        (all-< worklist (alen1 'done-array done-array))
                        (all-< worklist dag-len)
                        (true-listp fns)
                        (natp nodenum))))
  (if (or (endp worklist)
          (not (mbt (array1p 'done-array done-array)))
          (not (mbt (nat-listp worklist)))
          (not (mbt (all-< worklist (alen1 'done-array done-array)))))
      t
    (let* ((possible-parent-nodenum (first worklist)))
      (if (aref1 'done-array done-array possible-parent-nodenum)
          ;;this node has already been checked:
          (nodenum-only-appears-in (rest worklist) dag-array dag-len nodenum fns done-array)
        (let ((expr (aref1 'dag-array dag-array possible-parent-nodenum)))
          (if (or (variablep expr)
                  (fquotep expr))
              ;;it's a variable or quoted constant, so it's not a parent of nodenum
              (nodenum-only-appears-in (rest worklist) dag-array dag-len nodenum fns
                                       (aset1 'done-array done-array possible-parent-nodenum t))
            ;;function call:
            (if (and (member nodenum (dargs expr)) ;fixme check that the appearance is kosher (e.g., second arg of nth where the first arg is a constant in the right range?  what do we have to have for soundness?)
                     (not (member-eq (ffn-symb expr) fns)))
                nil
;check the children:
              (nodenum-only-appears-in (append-atoms (dargs expr) (rest worklist))
                                       dag-array dag-len nodenum fns
                                       (aset1 'done-array done-array possible-parent-nodenum t)))))))))

(local (in-theory (disable STRIP-CARS)))

(defthm assoc-equal-when-subsetp-equal-of-strip-cars
  (implies (and (subsetp-equal keys (strip-cars alist))
                (member-equal key keys)
                (alistp alist))
           (assoc-equal key alist))
  :hints (("Goal" :in-theory (enable ;ASSOC-EQUAL-IFF
                              strip-cars memberp subsetp-equal))))

;returns a var to elim, or nil to indicate failure to find one
;fixme don't re-search the literals for each var...
;fixme can't use the parent-array because that may include parents that are not used by any literals?
(defund var-okay-to-elim (vars dag-array dag-len dag-variable-alist literal-nodenums)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-variable-alistp dag-variable-alist dag-len)
                              (subsetp-equal vars (strip-cars dag-variable-alist))
                              (nat-listp literal-nodenums)
                              (consp literal-nodenums)
                              (all-< literal-nodenums dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (integerp-of-maxelem-when-all-integerp
                                                         natp-of-lookup-equal-when-dag-variable-alistp)
                                                        (natp))))))
  (if (endp vars)
      nil
    (let* ((var (first vars))
           (nodenum (lookup-eq-safe var dag-variable-alist))
           (max-literal-nodenum (maxelem literal-nodenums))
           )
      (if (nodenum-only-appears-in literal-nodenums dag-array dag-len nodenum '(nth true-listp len)
                                   (make-empty-array 'done-array (+ 1 max-literal-nodenum))
                                   ) ;fffixme make sure the nths are always of constants..
          var
        (var-okay-to-elim (rest vars) dag-array dag-len dag-variable-alist literal-nodenums)))))

;may be nil, which is a symbol
(defthm symbolp-of-var-okay-to-elim
  (implies (symbol-listp vars)
           (symbolp (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)))
  :hints (("Goal" :in-theory (enable var-okay-to-elim))))

(defthm member-equal-of-var-okay-to-elim
  (implies (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)
           (member-equal (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums) vars))
  :hints (("Goal" :in-theory (enable var-okay-to-elim))))

(defthm member-equal-of-var-okay-to-elim-gen
  (implies (and (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)
                (subsetp-equal vars vars2))
           (member-equal (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)
                    vars2))
  :hints (("Goal" :use (:instance member-equal-of-var-okay-to-elim)
           :in-theory (disable member-equal-of-var-okay-to-elim))))

;try to deprecate?
(defun axe-prover-hints (runes
                         rule-alist ;was rules
                         interpreted-function-alist analyzed-function-table)
  (s :runes runes
     (s :rule-alist rule-alist
        (s :interpreted-function-alist interpreted-function-alist
           (s :analyzed-function-table analyzed-function-table ;think about this
              nil)))))

;; (defun check-integerp (caller item)
;;   (declare (xargs :guard t))
;;   (if (integerp item)
;;       item
;;     (prog2$ (cw "Error in ~x0: Expected an integer but got ~x1." caller item)
;;             (break$)
;; ;            (hard-error caller nil nil)
;;             )))

;strip off any number of nested calls to not
;returns the "core" nodenum, or nil if the "core" is a constant
(defund strip-nots (nodenum-or-quotep dag-array-name dag-array)
  (declare (xargs :guard (if (natp nodenum-or-quotep)
                             (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                           t)
                  :measure (nfix nodenum-or-quotep)))
  (if (not (natp nodenum-or-quotep)) ;(quotep nodenum-or-quotep)
      nil
    (let ((expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
      (if (quotep expr)
          nil
        (if (and (call-of 'not expr)
                 (= 1 (len (dargs expr)))
                 (not (consp (darg1 expr))) ;todo: other case?
                 )
            (if (not (and (natp (darg1 expr))
                          (mbt (< (darg1 expr) nodenum-or-quotep))))
                :error
              ;; keep looking:
              (strip-nots (darg1 expr) dag-array-name dag-array))
          nodenum-or-quotep ;we've found the "core" node
          )))))

(defthm natp-of-strip-nots
  (implies (and (strip-nots nodenum-or-quotep dag-array-name dag-array)
                (if (natp nodenum-or-quotep)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t))
           (natp (strip-nots nodenum-or-quotep dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable strip-nots))))

(defthm strip-nots-when-consp
  (implies (consp nodenum-or-quotep)
           (equal (strip-nots nodenum-or-quotep dag-array-name dag-array)
                  nil))
  :hints (("Goal" :in-theory (enable strip-nots))))

(defthm <-of-strip-nots
  (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                (if (natp nodenum-or-quotep)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t)
                (strip-nots nodenum-or-quotep dag-array-name dag-array))
           (< (strip-nots nodenum-or-quotep dag-array-name dag-array) dag-len))
  :hints (("Goal" :in-theory (enable strip-nots))))

;;;
;;; strip-nots-and-maybe-extend
;;;

;; Strip NOTs and add the resulting nodenum to ACC (if the stripped thing is a constant, just return ACC).
(defund strip-nots-and-maybe-extend (nodenum-or-quotep dag-array-name dag-array acc)
  (declare (xargs :guard (if (natp nodenum-or-quotep)
                             (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                           t)))
  (let ((res (strip-nots nodenum-or-quotep dag-array-name dag-array)))
    (if res
        (cons res acc)
      acc)))

(defthm strip-nots-and-maybe-extend-when-consp
  (implies (consp nodenum-or-quotep)
           (equal (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc)
                  acc))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

(defthm true-listp-of-strip-nots-and-maybe-extend
  (equal (true-listp (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

(defthm all-natp-of-strip-nots-and-maybe-extend
  (implies (and (dargp nodenum-or-quotep)
                (if (not (consp nodenum-or-quotep))
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t))
           (equal (all-natp (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc))
                  (all-natp acc)))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

(defthm all-<-of-strip-nots-and-maybe-extend
  (implies (and (all-< acc dag-len)
                (dargp-less-than nodenum-or-quotep dag-len)
                (if (natp nodenum-or-quotep)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t))
           (all-< (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc) dag-len))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

;;;
;;; strip-nots-lst
;;;

;returns a list of nodenums (omits constants and nodenums of constants)
(defund strip-nots-lst (nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp nodenums)
                              (all-< nodenums dag-len))))
  (if (endp nodenums)
      nil
    (let ((res (strip-nots (first nodenums) dag-array-name dag-array)))
      (if res
          (cons res
                (strip-nots-lst (rest nodenums) dag-array-name dag-array dag-len))
        (strip-nots-lst (rest nodenums) dag-array-name dag-array dag-len)))))

(defthm all-natp-of-strip-nots-lst
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (nat-listp nodenums)
                (all-< nodenums dag-len))
           (all-natp (strip-nots-lst nodenums dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable strip-nots-lst nat-listp))))

;;;
;;; maybe-add-split-candidates
;;;

;; Possibly extends ACC with one or more nodenums to consider for splitting.  The
;; nodenums returned should not have exprs that are calls of NOT.
;; TODO: Consider splitting on arguments of boolfix.
(defund maybe-add-split-candidates (expr dag-array-name dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-dag-exprp dag-len ;upper bound
                                         expr))
                  :guard-hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0 car-becomes-nth-of-0)
                                 :do-not '(generalize eliminate-destructors))))
           (ignore dag-len))
  (if (variablep expr)
      acc
    (let* ((fn (ffn-symb expr)))
      (if (eq 'quote fn) ;can this happen?
          acc
        (let ((args (dargs expr)))
          ;;instead of skipping the nots, just include not as a function here?  then x will have a smaller size than (not x) in the size array
          (cond ((and (or (eq 'myif fn) (eq 'if fn))
                      (= 3 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array acc))
                ((and (eq fn 'bvif)
                      (= 4 (len args)))
                 (strip-nots-and-maybe-extend (second args) dag-array-name dag-array acc)) ;the test of the bvif is arg2
                ((and (eq fn 'bool-to-bit) ;new
                      (= 1 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array acc))
                ;; might we ever not want to split on the argument of a boolor or booland?
                ;; should we split for a boolxor?
;fffixme the args to booland (say) may be boolands, so we want to strip the bool ops (not just nots!) from them too. i guess we'll take the smallest node, but we may waste time (when using this to split a miter) checking whether these booland nodes (which we should never split on) have both true and false test cases...
                ((and (member-eq fn '(boolor booland boolxor))
                      (= 2 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array
                                              (strip-nots-and-maybe-extend (second args) dag-array-name dag-array acc)))
                ;;which one should we choose?
                ((and (eq fn 'boolif)
                      (= 3 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array
                                              (strip-nots-and-maybe-extend (second args) dag-array-name dag-array
                                                                           (strip-nots-and-maybe-extend (third args) dag-array-name dag-array acc))))
                ;;equality of a pred and something else..
                ((and (eq fn 'iff) ;had 'equal here but the prover had trouble using the fact that the arg was non-nil
                      (= 2 (len args)))
                 (let ((arg1 (first args)))
                   (if (and (integerp arg1)
                            (let ((arg1-expr (aref1 dag-array-name dag-array arg1)))
                              (and (consp arg1-expr)
                                   ;; Do we need this check?:
                                   ;;(member-eq (ffn-symb arg1-expr) *known-predicates-except-not-basic*) ;or pass in a list of known booleans
                                   )))
                       (strip-nots-and-maybe-extend arg1 dag-array-name dag-array acc) ;fixme what about arg2?
                     (let ((arg2 (second args)))
                       (if (and (integerp arg2)
                                (let ((arg2-expr (aref1 dag-array-name dag-array arg2)))
                                  (and (consp arg2-expr)
                                       ;; Do we need this check?:
                                       ;;(member-eq (ffn-symb arg2-expr) *known-predicates-except-not-basic*) ;or pass in a list of known booleans
                                       )))
                           (strip-nots-and-maybe-extend arg2 dag-array-name dag-array acc)
                         acc)))))
                (t acc)))))))

(defthm true-listp-of-maybe-add-split-candidates
  (equal (true-listp (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable maybe-add-split-candidates))))

(defthm all-natp-of-maybe-add-split-candidates
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (bounded-dag-exprp dag-len ;upper bound
                           expr)
                (all-natp acc))
           (all-natp (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc)))
  :hints (("Goal" :cases ((integerp (nth '0 (dargs$inline expr))))
           :in-theory (e/d (maybe-add-split-candidates
                            car-becomes-nth-of-0
                            bounded-dag-exprp
                            ;STRIP-NOTS-AND-MAYBE-EXTEND
                            ;;<-of-+-of-1-when-integers
                            NATP-OF-+-OF-1-ALT)
                           (dargp natp)))))

(defthm all-<-of-maybe-add-split-candidates
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (bounded-dag-exprp dag-len ;upper bound
                           expr)
                (all-< acc dag-len))
           (all-< (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc)
                  dag-len))
  :hints (("Goal" :cases ((integerp (nth '0 (dargs$inline expr))))
           :in-theory (e/d (maybe-add-split-candidates
                            car-becomes-nth-of-0
                            bounded-dag-exprp
                            ;STRIP-NOTS-AND-MAYBE-EXTEND
                            ;;<-of-+-of-1-when-integers
                            NATP-OF-+-OF-1-ALT)
                           (dargp natp)))))

;; (defthm all-natp-of-maybe-add-split-candidates
;;   (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (bounded-dag-exprp dag-len ;upper bound
;;                            expr))
;;            (equal (all-natp (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc))
;;                   (all-natp acc)))
;;   :hints (("Goal" :in-theory (enable maybe-add-split-candidates BOUNDED-DAG-EXPRP DAG-EXPRP0))))

;; Similar to get-args-not-done and especially to get-unexamined-nodenum-args.
(defund extend-with-not-done-args (args result-array-name result-array acc)
  (declare (xargs :guard (and (array1p result-array-name result-array)
                              (true-listp args)
                              (all-dargp-less-than args (alen1 result-array-name result-array)))))
  (if (endp args)
      acc
    (let* ((arg (first args)))
      (if (or (consp arg) ;it's a quotep, so skip it
              (aref1 result-array-name result-array arg) ;it's tagged as done, so skip it
              )
          (extend-with-not-done-args (rest args) result-array-name result-array acc)
        ;; add the arg:
        (extend-with-not-done-args (rest args) result-array-name result-array (cons arg acc))))))

(defthm nat-listp-of-extend-with-not-done-args
  (implies (and (nat-listp acc)
                (all-dargp args))
           (nat-listp (extend-with-not-done-args args result-array-name result-array acc)))
  :hints (("Goal" :in-theory (enable nat-listp extend-with-not-done-args))))

(defthm all-<-of-extend-with-not-done-args
  (implies (and (all-< acc bound)
                (all-dargp-less-than args bound))
           (all-< (extend-with-not-done-args args result-array-name result-array acc) bound))
  :hints (("Goal" :in-theory (enable extend-with-not-done-args))))

(local (in-theory (disable nat-listp)))

;this never adds to acc any nodes that are calls of not
;the result may contain duplicates
;; TODO: Use worklist-array and make this a standard worklist algorithm?
(defund find-node-to-split-candidates-work-list (worklist dag-array-name dag-array dag-len
                                                          done-array ;tracks which nodenums we have already considered
                                                          acc)
  (declare (xargs :measure (make-ord 1
                                     (+ 1 ;coeff must be positive
                                        (if (not (natp (alen1 'done-array done-array)))
                                            0
                                          (+ 1 (- (alen1 'done-array done-array)
                                                  (num-handled-nodes 'done-array done-array)))))
                                     (len worklist))
                  :guard (and (nat-listp worklist)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (array1p 'done-array done-array)
                              (all-< worklist (alen1 'done-array done-array))
                              (all-< worklist dag-len))))
  (if (or (endp worklist)
          (not (mbt (array1p 'done-array done-array)))
          (not (mbt (nat-listp worklist)))
          (not (mbt (all-< worklist (alen1 'done-array done-array)))))
      acc
    (let ((nodenum (first worklist)))
      (if (aref1 'done-array done-array nodenum)
          (find-node-to-split-candidates-work-list (rest worklist) dag-array-name dag-array dag-len done-array acc)
        (let* ((expr (aref1 dag-array-name dag-array nodenum))
               (acc (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc))) ;can this add more than one candidate?
          (find-node-to-split-candidates-work-list (if (or (variablep expr)
                                                           (quotep expr))
                                                       worklist
;fixme could just add all nodes to the worklist (would save arefs at the expense of consing) - similar changes elsewhere?
;fixme could tag nodes as soon as they are added to the worklist? might prevent them from being added more than once...
                                                     (extend-with-not-done-args (dargs expr) 'done-array done-array worklist))
                                                   dag-array-name dag-array dag-len
                                                   (aset1-safe 'done-array done-array nodenum t)
                                                   acc))))))

(defthm true-listp-of-find-node-to-split-candidates-work-list
  (equal (true-listp (find-node-to-split-candidates-work-list worklist dag-array-name dag-array dag-len done-array acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable find-node-to-split-candidates-work-list))))

(defthm not-<-of-car-when-nat-listp
  (Implies (and (syntaxp k)
                (<= k 0)
                (nat-listp x))
           (not (< (CAR x) k)))
  :hints (("Goal" :in-theory (enable nat-listp))))

(defthm all-natp-of-find-node-to-split-candidates-work-list
  (implies (and (all-natp acc)
                (nat-listp worklist)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (array1p 'done-array done-array)
                (all-< worklist (alen1 'done-array done-array))
                (all-< worklist dag-len))
           (all-natp (find-node-to-split-candidates-work-list worklist dag-array-name dag-array dag-len done-array acc)))
  :hints (("Goal" :in-theory (enable find-node-to-split-candidates-work-list))))

(defund smallest-size-node-aux (nodenums current-smallest-size current-smallest-node size-array size-array-len)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (array1p 'size-array size-array)
                              (natp size-array-len)
                              (<= size-array-len
                                  (alen1 'size-array size-array))
                              (all-< nodenums size-array-len)
                              (natp current-smallest-size)
                              )))
  (if (endp nodenums)
      current-smallest-node
    (let* ((next-nodenum (first nodenums))
           (next-size (nfix (aref1 'size-array size-array next-nodenum)))) ;todo: drop the nfix
      (if (< next-size current-smallest-size)
          (smallest-size-node-aux (rest nodenums) next-size next-nodenum size-array size-array-len)
        (smallest-size-node-aux (rest nodenums) current-smallest-size current-smallest-node size-array size-array-len)))))

;nodenums must be non-nil
;returns a nodenum
(defund smallest-size-node (nodenums size-array size-array-len)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (consp nodenums)
                              (array1p 'size-array size-array)
                              (natp size-array-len)
                              (<= size-array-len
                                  (alen1 'size-array size-array))
                              (all-< nodenums size-array-len)
                              )))
  (let* ((first-node (first nodenums))
         (first-size (nfix (aref1 'size-array size-array first-node)))) ;todo: drop the nfix?
    (smallest-size-node-aux (rest nodenums) first-size first-node size-array size-array-len)))

(defthm all-natp-of-merge-<
  (implies (and (all-natp l1)
                (all-natp l2)
                (all-natp acc))
           (all-natp (merge-< l1 l2 acc))))

(defthm eqlable-listp-of-merge-<
  (implies (and (eqlable-listp l1)
                (eqlable-listp l2)
                (eqlable-listp acc))
           (eqlable-listp (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<))))

(defthm eqlable-listp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (eqlable-listp acc)
                (eqlable-listp lst))
           (eqlable-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm eqlable-listp-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (eqlable-listp acc)
                (eqlable-listp lst))
           (eqlable-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm eqlable-listp-of-mv-nth-0-of-split-list-fast
  (Implies (EQLABLE-LISTP LST)
           (EQLABLE-LISTP (MV-NTH 0 (SPLIT-LIST-FAST LST))))
  :hints (("Goal" :in-theory (enable SPLIT-LIST-FAST))))

(defthm eqlable-listp-of-mv-nth-1-of-split-list-fast
  (implies (eqlable-listp lst)
           (eqlable-listp (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm eqlable-listp-of-merge-sort-<
  (implies (and (eqlable-listp lst)
                (true-listp lst))
           (eqlable-listp (merge-sort-< lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-sort-<) ()))))

(defthm eqlable-listp-when-all-natp
  (implies (and (all-natp x)
                (true-listp x))
           (eqlable-listp x)))

(defthm all-<-of-find-node-to-split-candidates-work-list
  (implies (and (all-< worklist dag-len)
                (all-< acc dag-len)
                (nat-listp worklist)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (array1p 'done-array done-array)
                (all-< worklist (alen1 'done-array done-array)))
           (all-< (find-node-to-split-candidates-work-list worklist dag-array-name dag-array dag-len
                                                           done-array ;tracks which nodenums we have already considered
                                                           acc)
                  dag-len))
  :hints (("Goal" :in-theory (e/d (find-node-to-split-candidates-work-list
                                   car-becomes-nth-of-0)
                                  (dargp-less-than
                                   ;member-of-cons ;todo
                                   )))))

;returns a nodenum to split on, or nil
;can we speed this up?
;destroys 'size-array and 'done-array
;;fffixme could the node to spit on ever be a literal?  or the negation of a literal? avoid that (could lead to loops)
;redid this now that we are not dropping unused nodes (thus, this now only examines nodes that support the literals)
;todo: have this return the size of the split node, so we know whether to print it?
(defun find-node-to-split-for-prover (dag-array-name dag-array dag-len
                                                     literal-nodenums ;can't be empty
                                                     )
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp literal-nodenums)
                              (consp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (< 0 dag-len) ;implied?
                              )
                  :guard-hints (("Goal" :in-theory (enable all-rationalp-when-all-natp)))))
  (let* ((max-literal-nodenum (maxelem literal-nodenums))
         (done-array (make-empty-array 'done-array (+ 1 max-literal-nodenum)))
         ;;won't include any nodes that are calls to not:
         (candidate-nodenums (find-node-to-split-candidates-work-list literal-nodenums dag-array-name dag-array dag-len done-array nil))
         (candidate-nodenums (merge-sort-< candidate-nodenums))
         (candidate-nodenums (remove-duplicates-from-grouped-list candidate-nodenums))
         (literals-after-stripping-nots (strip-nots-lst literal-nodenums dag-array-name dag-array dag-len))
         (literals-after-stripping-nots (merge-sort-< literals-after-stripping-nots))
         ;remove dups from literals-after-stripping-nots?
         ;;fixme take advantage of the sorting to call a linear-time version of this:
         (candidate-nodenums (set-difference$ candidate-nodenums literals-after-stripping-nots)))
    (if (endp candidate-nodenums)
        nil
      (if (endp (rest candidate-nodenums))
          (first candidate-nodenums) ;only one candidate, no need to compare sizes
        (let* ((size-array (size-array-for-sorted-nodes candidate-nodenums dag-array-name dag-array dag-len 'size-array)))
          (smallest-size-node candidate-nodenums size-array dag-len))))))

;no sense monitoring definition rules.. (could also skip rules without hyps, if any)
;; (defun keep-rewrite-rule-names (runes)
;;   (if (endp runes)
;;       nil
;;     (let ((rune (car runes)))
;;       (if (and (consp rune)
;;                (eq :rewrite (car rune)))
;;           (cons (second rune) ;now strips off the rule class, since monitored runes are just symbols
;;                 (keep-rewrite-rule-names (cdr runes)))
;;         ;skip it (it's probably a :definition):
;;         (keep-rewrite-rule-names (cdr runes))))))

;looks for the if nest that results from the macro OR
;now also handles boolor ! ;Fri Feb 12 12:54:05 2010
(defun get-disjuncts-from-term (term)
  (if (and (call-of 'if term)
           (equal (farg1 term) (farg2 term)))
      (cons (farg1 term) ;should we dive into this term too?
            (get-disjuncts-from-term (farg3 term)))
    (if (call-of 'boolor term)
        (append (get-disjuncts-from-term (farg1 term))
                (get-disjuncts-from-term (farg2 term)))
      (list term))))

;returns a list of conjuncts (terms) whose conjunction is equivalent to (not term)
;only preserves iff, not equality?
(defun conjuncts-for-negation (term)
  ;;uses the fact that (not (or x y)) is (and (not x) (not y))
  (negate-terms (get-disjuncts-from-term term)))

;defforall could do these too?
(defthm all-natp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-natp lst)
                (all-natp acc)
                (<= (len tail) (len lst)))
           (all-natp (mv-nth 0 (split-list-fast-aux lst tail acc)))))

(defthm all-natp-of-mv-nth-0-of-split-list-fast
  (implies (all-natp lst)
           (all-natp (mv-nth 0 (split-list-fast lst))))
  :hints (("Goal" :in-theory (e/d (split-list-fast) ()))))

(defthm all-natp-of-mv-nth-1-of-split-list-fast-aux
  (implies (all-natp lst)
           (all-natp (mv-nth 1 (split-list-fast-aux lst tail acc)))))

(defthm all-natp-of-mv-nth-1-split-list-fast
  (implies (all-natp lst)
           (all-natp (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (e/d (split-list-fast) (SPLIT-LIST-FAST-AUX)))))

;; ;fixme defforall should do this?
;; (defthm all-natp-of-revappend
;;   (implies (and (all-natp x)
;;                 (all-natp y))
;;            (all-natp (revappend x y)))
;;   :hints (("Goal" :in-theory (enable revappend))))

;; ;; returns (mv new-parent-expr dag-parent-array)
;; ;fixme this was missing NOT as a boolean context; make sure the contexts this checks are in sync with the contexts used to find the node to split on
;; (defun replace-nodenum-with-t-in-boolean-contexts-in-parent-expr (nodenum parent-expr parent-nodenum dag-parent-array)
;; ;fixme keep this in sync with find-node-to-split-candidates
;;   (let ((fn (ffn-symb parent-expr))
;;         (args (fargs parent-expr)))
;;     (cond ((or (eq 'if fn) (eq 'myif fn))
;;            (mv `(,fn ,(if (eql nodenum (first args)) *t* (first args))
;;                      ,(second args)
;;                      ,(third args))
;;                (if (and (not (eql nodenum (second args)))
;;                         (not (eql nodenum (third args))))
;;                    ;;nodenum is no longer a child:
;;                    (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)
;;                  dag-parent-array)))
;;           ((eq 'bvif fn)
;;            (mv `(,fn ,(first args)
;;                      ,(if (eql nodenum (second args)) *t* (second args))
;;                      ,(third args)
;;                      ,(fourth args))
;;                (if (and (not (eql nodenum (first args)))
;;                         (not (eql nodenum (third args)))
;;                         (not (eql nodenum (fourth args))))
;;                    ;;nodenum is no longer a child:
;;                    (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)
;;                  dag-parent-array)))
;;           ((eq 'bool-to-bit fn)
;;            (mv `(,fn ,(if (eql nodenum (first args)) *t* (first args))) ;fixme if its a parent it must have nodenum as the only arg...
;;                ;;nodenum is no longer a child:
;;                (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)))
;;            ((member-eq fn '(boolor booland boolxor))
;;            (mv `(,fn ,(if (eql nodenum (first args)) *t* (first args))
;;                      ,(if (eql nodenum (second args)) *t* (second args)))
;;                ;;nodenum is no longer a child:
;;                (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)))
;;           ((eq fn 'boolif)
;;            (mv `(,fn ,(if (eql nodenum (first args)) *t* (first args))
;;                      ,(if (eql nodenum (second args)) *t* (second args))
;;                      ,(if (eql nodenum (third args)) *t* (third args)))
;;                ;;nodenum is no longer a child:
;;                (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)))
;;           ((eq fn 'iff)
;;            (mv `(,fn ,(if (eql nodenum (first args)) *t* (first args))
;;                      ,(if (eql nodenum (second args)) *t* (second args)))
;;                ;;nodenum is no longer a child:
;;                (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)))
;;           ((eq fn 'not)
;;            (mv `(,fn ,(if (eql nodenum (first args))  ;if not, it's an error, since this node is a parent?!
;;                           *t* (first args)))
;;                ;;nodenum is no longer a child:
;;                (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)))
;;           (t (mv parent-expr dag-parent-array)))))

;; (skip- proofs (verify-guards replace-nodenum-with-t-in-boolean-contexts-in-parent-expr))

;; ;; Returns (mv dag-array dag-parent-array)
;; ;; has to update the parent array since some nodes are losing children
;; (defun replace-nodenum-with-t-in-boolean-parents (parent-nodenums nodenum dag-array dag-parent-array)
;;   (if (endp parent-nodenums)
;;       (mv dag-array dag-parent-array)
;;     (let* ((parent-nodenum (first parent-nodenums))
;;            (parent-expr (aref1 'dag-array dag-array parent-nodenum)))
;;       (mv-let
;;        (new-parent-expr dag-parent-array)
;;        (replace-nodenum-with-t-in-boolean-contexts-in-parent-expr nodenum parent-expr parent-nodenum dag-parent-array)
;;        (replace-nodenum-with-t-in-boolean-parents (rest parent-nodenums) nodenum
;;                                                   (aset1-safe 'dag-array dag-array parent-nodenum new-parent-expr)
;;                                                   dag-parent-array)))))

;; (skip- proofs (verify-guards replace-nodenum-with-t-in-boolean-parents))

;; ;fixme keep a change-flg and throw an error if nothing changes?
;; ;rename to not mention "contexts"
;; ;; Returns (mv dag-array dag-parent-array)
;; (defun replace-nodenum-with-t-in-boolean-contexts (nodenum dag-array dag-parent-array)
;;   (let ((parent-nodenums (aref1 'dag-parent-array dag-parent-array nodenum)))
;;     (replace-nodenum-with-t-in-boolean-parents parent-nodenums nodenum dag-array dag-parent-array)))

;; (skip- proofs (verify-guards replace-nodenum-with-t-in-boolean-contexts))

;; ;uses eql as the test
;; ;replace is already defined in the main lisp package
;; (defun my-replace (old new lst)
;;   (declare (xargs :guard (and (or (eqlablep old)
;;                                   (eqlable-listp lst))
;;                                (true-listp lst))))
;;   (if (endp lst)
;;       nil
;;     (let ((item (first lst)))
;;       (if (eql old item)
;;           (cons new (my-replace old new (cdr lst)))
;;         (cons item (my-replace old new (cdr lst)))))))

;; ;; Returns (mv dag-array dag-parent-array)
;; ;; has to update the parent array since some nodes are losing children
;; (defun replace-nodenum-with-nil-in-parents (parent-nodenums nodenum dag-array dag-parent-array)
;;   (if (endp parent-nodenums)
;;       (mv dag-array dag-parent-array)
;;     (let* ((parent-nodenum (first parent-nodenums))
;;            (parent-expr (aref1 'dag-array dag-array parent-nodenum)) ;we know it will be a function call
;;            (fn (ffn-symb parent-expr))
;;            (args (fargs parent-expr)))
;;       (mv (aset1-safe 'dag-array dag-array parent-nodenum (cons fn (my-replace nodenum *nil* args)))
;;           (drop-parent-relationship parent-nodenum nodenum 'dag-parent-array dag-parent-array)))))

;; (skip- proofs (verify-guards replace-nodenum-with-nil-in-parents))

;; ;; Returns (mv dag-array dag-parent-array)
;; ;changes all the parents of nodenum
;; ;updates the parent array accordingly
;; ;this code (for nil) is simpler than the analogous code for t, because nil is only one value, whereas t really means non-nil, and it's only sounds to put in t for val in boolean contexts when all we know is that val is non-nil
;; (defun replace-nodenum-with-nil (nodenum dag-array dag-parent-array)
;;   (let ((parent-nodenums (aref1 'dag-parent-array dag-parent-array nodenum)))
;;     (replace-nodenum-with-nil-in-parents parent-nodenums nodenum dag-array dag-parent-array)))

;; (skip- proofs (verify-guards replace-nodenum-with-nil))

;disble?
(defthm natp-of-car-when-nat-listp-type
  (implies (and (nat-listp x)
                (consp x))
           (natp (car x)))
  :rule-classes :type-prescription)

(defthm nat-listp-when-all-natp
  (implies (all-natp x)
           (equal (nat-listp x)
                  (true-listp x)))
  :hints (("Goal" :in-theory (enable nat-listp all-natp))))

(defthmd dargp-of-car-when-all-natp
  (implies (all-natp x)
           (equal (dargp (car x))
                  (consp x))))

(defthm all-<=-all-of-get-unexamined-nodenum-args
  (implies (and (all-<=-all (keep-atoms args) worklist)
                (all-<=-all acc worklist))
           (all-<=-all (get-unexamined-nodenum-args args worklist-array acc) worklist))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args keep-atoms))))


;;(ALL-<=-ALL (DARGS (AREF1 'DAG-ARRAY DAG-ARRAY nodenum)) WORKLIST)

(defthm all-<=-of-keep-atoms
  (implies (and (all-dargp-less-than args (+ 1 nodenum))
                (natp nodenum))
           (all-<= (keep-atoms args) nodenum))
  :hints (("Goal" :in-theory (enable all-dargp-less-than keep-atoms))))

(defthm all-<=-of-keep-atoms-of-dargs
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (consp (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))
                (NOT (EQUAL 'QUOTE (CAR (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))))
                (natp nodenum)
                (< nodenum dag-len))
           (all-<= (keep-atoms (dargs (aref1 'dag-array dag-array nodenum)))
                   nodenum))
  :hints (("Goal" :use (:instance all-<=-of-keep-atoms (args (dargs (aref1 'dag-array dag-array nodenum))))
           :in-theory (disable all-<=-of-keep-atoms))))

(defthm ALL-<=-ALL-when-ALL-<=-ALL-of-cdr-arg2
  (implies (and (ALL-<=-ALL x (cdr y))
                )
           (equal (ALL-<=-ALL x y)
                  (or (not (consp y))
                      (all-<= x (car y)))))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm all-<=-all-of-keep-atoms-of-dargs
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (consp (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))
                (NOT (EQUAL 'QUOTE (CAR (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))))
                (natp nodenum)
                (< nodenum dag-len)
                (<=-all nodenum nodenums)
                )
           (all-<=-all (keep-atoms (dargs (aref1 'dag-array dag-array nodenum)))
                       nodenums))
  :hints (("subgoal *1/3"
           :use (:instance all-<=-of-keep-atoms-of-dargs)
           :in-theory (e/d ()
                           (ALL-<-OF-KEEP-ATOMS
                            all-<=-of-keep-atoms-of-dargs
                            all-<=-of-keep-atoms
                            all-<-of-keep-atoms-of-dargs-when-bounded-dag-exprp
                            ;;all-dargp-less-than-of-args-when-bounded-dag-exprp
                            )))))

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing the substitution indicated by TRANSLATION-ARRAY.
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; TODO: this could compute ground terms - but the caller would need to check for quoteps in the result
;; TODO: We could stop once we hit a node smaller than any node which is changed in the translation-array?  track the smallest node with a pending change.  no smaller node needs to be changed?
(defund rebuild-nodes-aux (worklist ;should be sorted
                           translation-array ;maps each nodenum to nil (unhandled) or a nodenum (maybe the nodenum itself) [or a quotep - no, not currently]
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                           worklist-array)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                              (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                              (= (alen1 'worklist-array worklist-array)
                                 (alen1 'translation-array translation-array)))
                  ;; For the measure, we first check whether the number of
                  ;; examined nodes goes up.  If not, we check that the length
                  ;; of the worklist goes down.
                  :measure (make-ord 1 (+ 1 (- (nfix (alen1 'worklist-array worklist-array))
                                               (num-examined-nodes (+ -1 (alen1 'worklist-array worklist-array))
                                                                   'worklist-array worklist-array)))
                                     (len worklist))
                  :verify-guards nil ; done below
                  ))
  (if (or (endp worklist)
          (not (and (mbt (array1p 'worklist-array worklist-array))
                    (mbt (all-natp worklist))
                    (mbt (all-< worklist (alen1 'worklist-array worklist-array))))))
      (mv (erp-nil) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let ((nodenum (first worklist)))
      (if (aref1 'translation-array translation-array nodenum)
          ;;This nodenum is being replaced, so we don't need to build any new
          ;;nodes (and it is already bound in translation-array):
          (rebuild-nodes-aux (rest worklist) translation-array
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                             ;; We mark the node as "examined" so it doesn't get added again:
                             (aset1 'worklist-array worklist-array nodenum :examined))
        (let ((expr (aref1 'dag-array dag-array nodenum)))
          (if (atom expr)
              ;;it's a variable, so no nodes need to be rebuilt:
              (rebuild-nodes-aux (rest worklist)
                                 (aset1 'translation-array translation-array nodenum nodenum)
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 ;; We mark the node as "examined" so it doesn't get added again:
                                 (aset1 'worklist-array worklist-array nodenum :examined))
            (if (fquotep expr)
                ;;it's a constant, so no nodes need to be rebuilt:
                (rebuild-nodes-aux (rest worklist)
                                   (aset1 'translation-array translation-array nodenum
                                               nodenum ;todo: i'd like to say expr here, but that could cause translation-array to map nodes to things other than nodenums (which the callers would need to handle -- e.g., if a literal maps to a quotep)
                                               )
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                   ;; We mark the node as "examined" so it doesn't get added again:
                                   (aset1 'worklist-array worklist-array nodenum :examined))
              ;;it's a function call:
              (let ((res (aref1 'worklist-array worklist-array nodenum)))
                (if (eq res :examined)
                    ;; The node has been examined, and since we are back to handling
                    ;; it again, we know that its children have already been examined
                    ;; and processed. So now we can process this node:
                    (b* (((mv erp new-args changep)
                          (translate-args-with-changep (dargs expr) translation-array))
                         ((when erp) (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                      (if changep
                          ;; TODO: It would be nice to evaluate ground terms here,
                          ;; but that could cause translation-array to map nodes to
                          ;; things other than nodenums (which the callers would
                          ;; need to handle -- e.g., if a literal maps to a quotep).
                          (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                            (add-function-call-expr-to-dag-array (ffn-symb expr) new-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                            (if erp
                                (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                              (rebuild-nodes-aux (rest worklist)
                                                 (aset1 'translation-array translation-array nodenum new-nodenum)
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 worklist-array)))
                        ;; No change, so the node maps to itself:
                        (rebuild-nodes-aux (rest worklist)
                                           (aset1 'translation-array translation-array nodenum nodenum)
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           worklist-array)))
                  ;; We expand the node. This node's children have not
                  ;; necessarily been processed, but if they've been examined,
                  ;; they've been fully processed.
                  (let* ((unexamined-args (get-unexamined-nodenum-args (dargs expr) worklist-array nil))
                         ;; TODO: Optimze the case where unexamined-args is nil?
                         (sorted-unexamined-args (merge-sort-< unexamined-args)))
                    (rebuild-nodes-aux (append sorted-unexamined-args worklist)
                                       translation-array
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       (aset1 'worklist-array worklist-array nodenum :examined))))))))))))

;move
(defthm SORTEDP-<=-of-cdr ;move
  (implies (SORTEDP-<= WORKLIST)
           (SORTEDP-<= (CDR WORKLIST))))

;dup
(defthm all-<=-when-all-<
  (implies (all-< x bound)
           (all-<= x bound))
  :hints (("Goal" :in-theory (enable all-< all-<=))))

(verify-guards rebuild-nodes-aux :hints (("Goal" :in-theory (e/d (<-of-car-when-all-< dargp-of-car-when-all-natp
                                                                                      all-<=-when-all-<)
                                                                 (dargp
                                                                  dargp-less-than
                                                                  SORTEDP-<=)))))

(def-dag-builder-theorems
  (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-aux))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-aux))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                (= (alen1 'worklist-array worklist-array)
                   (alen1 'translation-array translation-array)))
           (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                   (mv-nth '1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-aux) (dargp)))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                (= (alen1 'worklist-array worklist-array)
                   (alen1 'translation-array translation-array)))
           (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                           (mv-nth 1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))
                                           (mv-nth 3 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-aux) (dargp)))))

;; Returns (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund rebuild-nodes (worklist ;should be sorted
                       translation-array ;maps each nodenum to nil (unhandled) or a nodenum (maybe the nodenum itself) [or a quotep - no, not currently]
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (consp worklist)
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))))
  (rebuild-nodes-aux worklist
                     translation-array
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     (make-empty-array 'worklist-array (alen1 'translation-array translation-array))))

(def-dag-builder-theorems
  (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                (nat-listp worklist)
                (consp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (translation-arrayp-aux n
                                   (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                (nat-listp worklist)
                (consp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (bounded-translation-arrayp-aux n
                                           (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                           (mv-nth 3 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

;; This throws an error if a node translates to a constant.
;; Returns (mv changed-nodes unchanged-nodes).
;; TODO: Compare to the renaming-array stuff.
(defund translate-nodes (nodenums translation-array changed-acc unchanged-acc)
  (declare (xargs :guard (and (true-listp nodenums)
                              (array1p 'translation-array translation-array)
                              (all-natp nodenums)
                              (all-< nodenums (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (true-listp changed-acc)
                              (true-listp unchanged-acc))
                  :guard-debug t
                  ))
  (if (endp nodenums)
      (mv changed-acc
          unchanged-acc)
    (b* ((nodenum (first nodenums))
         (res (aref1 'translation-array translation-array nodenum))
         ;; for guard proof:
         ((when (not (natp res))) ;can't happen?
          (er hard? 'translate-nodes "A literal translated to a non-natp.")
          ;; for ease of reasoning:
          (mv (append (repeat (len nodenums) 0) changed-acc)
              unchanged-acc)))
      (if (= res nodenum)
          ;; no change:
          (translate-nodes (rest nodenums) translation-array changed-acc (cons nodenum unchanged-acc))
        (progn$ ;; (cw "~x0 became ~x1.~%" nodenum res)
                (translate-nodes (rest nodenums) translation-array (cons res changed-acc) unchanged-acc))))))

;(local (in-theory (disable reverse-removal)))

;rename
(defthm len-of-translate-nodes
  (equal (+ (len (mv-nth 0 (translate-nodes nodenums translation-array changed-acc unchanged-acc)))
            (len (mv-nth 1 (translate-nodes nodenums translation-array changed-acc unchanged-acc))))
         (+ (len nodenums)
            (len changed-acc)
            (len unchanged-acc)))
  :hints (("Goal" :in-theory (enable translate-nodes))))

(local
 (defthm nat-listp-of-append
   (implies (and (nat-listp x)
                 (nat-listp y))
            (nat-listp (append x y)))
   :hints (("Goal" :in-theory (enable nat-listp)))))

(local
 (defthm nat-listp-of-repeat
   (implies (natp x)
            (nat-listp (repeat n x)))
   :hints (("Goal" :in-theory (enable nat-listp repeat)))))

(local
 (defthm all-<-of-repeat
   (implies (< x bound)
            (all-< (repeat n x) bound))
   :hints (("Goal" :in-theory (enable nat-listp repeat)))))

(defthm nat-listp-of-mv-nth-0-of-translate-nodes
  (implies (and (nat-listp nodenums)
                (nat-listp changed-acc)
                (nat-listp unchanged-acc))
           (nat-listp (mv-nth 0 (translate-nodes nodenums translation-array changed-acc unchanged-acc))))
  :hints (("Goal" :in-theory (enable translate-nodes))))

(defthm nat-listp-of-mv-nth-1-of-translate-nodes
  (implies (and (nat-listp nodenums)
                (nat-listp changed-acc)
                (nat-listp unchanged-acc))
           (nat-listp (mv-nth 1 (translate-nodes nodenums translation-array changed-acc unchanged-acc))))
  :hints (("Goal" :in-theory (enable translate-nodes))))

(defthm true-listp-of-mv-nth-0-of-translate-nodes
  (implies (true-listp changed-acc)
           (true-listp (mv-nth 0 (translate-nodes nodenums translation-array changed-acc unchanged-acc))))
  :hints (("Goal" :in-theory (enable translate-nodes))))

(defthm true-listp-of-mv-nth-1-of-translate-nodes
  (implies (true-listp unchanged-acc)
           (true-listp (mv-nth 1 (translate-nodes nodenums translation-array changed-acc unchanged-acc))))
  :hints (("Goal" :in-theory (enable translate-nodes))))

(defthm all-<-of-mv-nth-0-of-translate-nodes
  (implies (and (posp bound)
                (all-< changed-acc bound)
                ;(all-< unchanged-acc bound)
                (array1p 'translation-array translation-array)
                (all-natp nodenums)
                (all-< nodenums (alen1 'translation-array translation-array))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound))
           (all-< (mv-nth 0 (translate-nodes nodenums translation-array changed-acc unchanged-acc)) bound))
  :hints (("Goal" :in-theory (enable translate-nodes))))

(defthm all-<-of-mv-nth-1-of-translate-nodes
  (implies (and (posp bound)
;(all-< changed-acc bound)
                (all-< unchanged-acc bound)
                (array1p 'translation-array translation-array)
                (all-natp nodenums)
                (all-< nodenums (alen1 'translation-array translation-array))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound))
           (all-< (mv-nth 1 (translate-nodes nodenums translation-array changed-acc unchanged-acc)) bound))
  :hints (("subgoal *1/3"
           :use (:instance <-OF-AREF1-WHEN-BOUNDED-TRANSLATION-ARRAYP-AUX
                           (nodenum (car nodenums))
                           (bound2 bound)
                           (nodenum2 (+ -1
                                        (ALEN1 'TRANSLATION-ARRAY
                                               TRANSLATION-ARRAY))))
           :in-theory (disable <-OF-AREF1-WHEN-BOUNDED-TRANSLATION-ARRAYP-AUX))
          ("Goal" :in-theory (enable translate-nodes))))

;; This turned out to seemingly always return all the literals as literals-greater-or-equal
;; ;; Returns (mv literals-less literals-greater-or-equal).
;; ;; Both return values have nodes in reverse order wrt the inputs.
;; (defund split-literals (literal-nodenums nodenum less-acc greater-or-equal-acc)
;;   (declare (xargs :guard (and (nat-listp literal-nodenums)
;;                               (natp nodenum)
;;                               (nat-listp less-acc)
;;                               (nat-listp greater-or-equal-acc))))
;;   (if (endp literal-nodenums)
;;       (mv less-acc greater-or-equal-acc)
;;     (let ((first-nodenum (first literal-nodenums)))
;;       (if (< first-nodenum nodenum)
;;           (split-literals (rest literal-nodenums)
;;                           nodenum
;;                           (cons first-nodenum less-acc)
;;                           greater-or-equal-acc)
;;         (split-literals (rest literal-nodenums)
;;                         nodenum
;;                         less-acc
;;                         (cons first-nodenum greater-or-equal-acc))))))

;; (defthm true-listp-of-mv-nth-0-of-split-literals
;;   (equal (true-listp (mv-nth 0 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc)))
;;          (true-listp less-acc))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm true-listp-of-mv-nth-1-of-split-literals
;;   (equal (true-listp (mv-nth 1 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc)))
;;          (true-listp greater-or-equal-acc))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm nat-listp-of-mv-nth-0-of-split-literals
;;   (implies (and (nat-listp literal-nodenums)
;;                 (nat-listp less-acc))
;;            (nat-listp (mv-nth 0 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm nat-listp-of-mv-nth-1-of-split-literals
;;   (implies (and (nat-listp literal-nodenums)
;;                 (nat-listp greater-or-equal-acc))
;;            (nat-listp (mv-nth 1 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm all-<-of-mv-nth-0-of-split-literals
;;   (implies (and (all-< literal-nodenums bound)
;;                 (all-< less-acc bound))
;;            (all-< (mv-nth 0 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))
;;                   bound))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm all-<=-of-mv-nth-1-of-split-literals
;;   (implies (and (all-< literal-nodenums bound)
;;                 (all-<= greater-or-equal-acc bound))
;;            (all-<= (mv-nth 1 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))
;;                    bound))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm all-<=-of-mv-nth-1-of-split-literals-main
;;   (implies (<=-all nodenum greater-or-equal-acc)
;;            (<=-all nodenum
;;                    (mv-nth 1 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm all-<-of-mv-nth-1-of-split-literals
;;   (implies (and (all-< literal-nodenums bound)
;;                 (all-< greater-or-equal-acc bound))
;;            (all-< (mv-nth 1 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))
;;                   bound))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;; (defthm +-of-len-of-mv-nth-0-of-split-literals-and-len-of-mv-nth-1-of-split-literals
;;   (equal (+ (len (mv-nth 0 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc)))
;;             (len (mv-nth 1 (split-literals literal-nodenums nodenum less-acc greater-or-equal-acc))))
;;          (+ (len literal-nodenums)
;;             (len less-acc)
;;             (len greater-or-equal-acc)))
;;   :hints (("Goal" :in-theory (enable split-literals))))

;move
(defthmd all-integerp-when-all-natp
  (implies (all-natp x)
           (all-integerp x)))

(defthm <-of-+-of-1-and-car-of-last-when-<=-all
  (implies (and (<=-all x lst)
                (consp lst))
           (< x (+ 1 (car (last lst))))))

;todo: nested induction
(defthm <=-all-of-merge-<
  (implies (and (<=-all a x)
                (<=-all a y)
                (<=-all a acc))
           (<=-all a (merge-< x y acc)))
  :hints (("Goal" :in-theory (enable merge-<))))

(defthm <=-all-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (<=-all a lst)
                (<=-all a tail)
                (<=-all a acc)
                (<= (len tail) (len lst))
                )
           (<=-all a (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm <=-all-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (<=-all a lst)
                (<=-all a tail)
                (<=-all a acc)
                (<= (len tail) (len lst))
                )
           (<=-all a (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm <=-all-of-mv-nth-0-of-split-list-fast
  (implies (<=-all a x)
           (<=-all a (mv-nth 0 (split-list-fast x))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm <=-all-of-mv-nth-1-of-split-list-fast
  (implies (<=-all a x)
           (<=-all a (mv-nth 1 (split-list-fast x))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm <=-all-of-merge-sort-<
  (implies (<=-all a x)
           (<=-all a (merge-sort-< x)))
  :hints (("Goal" :in-theory (enable merge-sort-<))))

;; A good ordering of substitutions would be to substitute the "smallest" term
;; (the one which will be at the bottom of the DAG after all the substs) into
;; the second smallest, then substitute that into the third smallest, and so
;; on.  Doing so means that only a little bit of structure needs to be rebuilt
;; each time.  A bad ordering would substitute the biggest/highest term (in
;; terms of where it will appear in the resuls) that can be substituted, then
;; put the second biggest into that (on the bottom), etc.  With such an
;; ordering, more and more structure gets rebuilt each time.

;; Returns (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;smashes 'translation-array (and 'tag-array ?)
;ffixme can the literal-nodenums returned ever contain a quotep?
;this could compute ground terms - but the caller would need to check for quoteps in the result
;doesn't change any existing nodes in the dag (just builds new ones)
;; TODO: Consider making a version of this for prover depth 0 which rebuilds
;; the array from scratch (since we can change existing nodes when at depth 0).
(defund rebuild-literals-with-substitution (literal-nodenums
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
  (b* (((when (not (consp literal-nodenums))) ;must check since we take the max below
        (mv (erp-nil) ;or perhaps this is an error.  can it happen?
            literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (sorted-literal-nodenums (merge-sort-< literal-nodenums)) ;; todo: somehow avoid doing this sorting over and over?  keep the list sorted?
       (max-literal-nodenum (car (last sorted-literal-nodenums)))
       ((when (< max-literal-nodenum nodenum-to-replace)) ;; may only happen when substituting for a var that doesn't appear in any other literal
        ;;No change, since nodenum-to-replace does not appear in any literal:
        (mv (erp-nil)
            literal-nodenums ;; the original literal-nodenums (so that the order is the same)
            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (translation-array (make-empty-array 'translation-array (+ 1 max-literal-nodenum)))
       ;; ensure that nodenum-to-replace gets replaced with new-nodenum:
       (translation-array (aset1 'translation-array translation-array nodenum-to-replace new-nodenum))
       ((mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (rebuild-nodes sorted-literal-nodenums ;; initial worklist, could use literal-nodenums instead
                       translation-array
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((when erp) (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((mv changed-literal-nodenums
            unchanged-literal-nodenums)
        (translate-nodes literal-nodenums ;; could use sorted-literal-nodenums instead
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

(defthm len-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (not (mv-nth 0 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
           (equal (len (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                  (len literal-nodenums)))
  :hints (("Goal" :in-theory (enable rebuild-literals-with-substitution))))

(local (in-theory (enable all-integerp-when-all-natp
                          natp-of-+-of-1-alt))) ;for the call of def-dag-builder-theorems just below

(def-dag-builder-theorems
  (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)
  (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((nat-listp literal-nodenums)
         (all-< literal-nodenums dag-len)
         (natp nodenum-to-replace)
         (< nodenum-to-replace dag-len)
         (natp new-nodenum)
         (< new-nodenum dag-len)))

;gen?
(defthm nat-listp-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp nodenum-to-replace)
                (nat-listp acc)
                (natp new-nodenum)
                (< new-nodenum dag-len)
                ;; (not (mv-nth 0 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                )
           (nat-listp (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))

(defthm true-listp-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (true-listp literal-nodenums)
           (true-listp (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))

(defthm all-<-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp nodenum-to-replace)
                (< nodenum-to-replace dag-len)
                (nat-listp acc)
                (natp new-nodenum)
                (< new-nodenum dag-len)
                ;; (not (mv-nth 0 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                (all-< acc dag-len)
                )
           (all-< (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))
                  (mv-nth 3 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))

;decides whether we should substitute (is it the nodenum of a var, and is it equated to a term that doesn't include itself?)
;returns (mv substp var nodenum-of-var)
;equated-thing is a quotep or nodenum
(defund nodenum-of-var-to-substp (nodenum-or-quotep equated-thing dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than nodenum-or-quotep dag-len)
                              (dargp-less-than equated-thing dag-len)))
           (ignore dag-len))
  (if (not (atom nodenum-or-quotep))
      (mv nil nil nil) ;must be a quotep
    (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
      (if (and (symbolp expr) ;must be a variable
               (not (quotep equated-thing)) ; an equality of a var and a constant should be used when rewriting.. (fixme allow this, to get rid of var=const when var appears nowhere else)
               ;;helps prevent loops?:
               (if (member nodenum-or-quotep (supporters-of-node equated-thing 'dag-array dag-array 'tag-array-for-supporters)) ;expensive?
                   (prog2$ (cw "Refusing to substitute for ~x0 because it is equated to something involving itself !!~%" expr) ;fixme print the terms involved?
                           nil)
                 t))
          (mv t expr nodenum-or-quotep)
        (mv nil nil nil)))))

;; Returns (mv foundp var nodenum-of-var equated-thing) where equated-thing will always be a nodenum.
;the awkwardness here is to avoid doing the aref more than once..
;what is we have (equal var1 var2)?  is there a way to tell which would be better to eliminate? maybe it doesn't matter
(defund find-var-and-expr-to-subst (lhs rhs dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than lhs dag-len)
                              (dargp-less-than rhs dag-len))))
  (mv-let (substp var nodenum-of-var)
    (nodenum-of-var-to-substp lhs rhs dag-array dag-len)
    (if substp
        (mv t var nodenum-of-var rhs)
      (mv-let (substp var nodenum-of-var)
        (nodenum-of-var-to-substp rhs lhs dag-array dag-len)
        (if substp
            (mv t var nodenum-of-var lhs)
          (mv nil nil nil nil))))))

(defthm natp-of-mv-nth-2-of-find-var-and-expr-to-subst
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
                (or (natp rhs)
                    (consp rhs))
                (or (natp lhs)
                    (consp lhs)))
           (natp (mv-nth 2 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst NODENUM-OF-VAR-TO-SUBSTP))))

(defthm <-of-mv-nth-2-of-find-var-and-expr-to-subst
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dargp-less-than lhs dag-len)
                (dargp-less-than rhs dag-len))
           (< (mv-nth 2 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
              dag-len))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst NODENUM-OF-VAR-TO-SUBSTP))))

(defthm natp-of-mv-nth-3-of-find-var-and-expr-to-subst
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
                (or (natp rhs)
                    (consp rhs))
                (or (natp lhs)
                    (consp lhs))
                (not (consp (mv-nth 3 (find-var-and-expr-to-subst lhs rhs dag-array dag-len)))))
           (natp (mv-nth 3 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst NODENUM-OF-VAR-TO-SUBSTP))))

(defthm <-of-mv-nth-3-of-find-var-and-expr-to-subst
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dargp-less-than lhs dag-len)
                (dargp-less-than rhs dag-len))
           (< (mv-nth 3 (find-var-and-expr-to-subst lhs rhs dag-array dag-len))
              dag-len))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst NODENUM-OF-VAR-TO-SUBSTP))))

(defthm nat-listp-of-remove-equal
  (implies (nat-listp x)
           (nat-listp (remove-equal a x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

(local (in-theory (disable REMOVE-EQUAL))) ;prevent inductions

;; Returns (mv foundp var nodenum-of-var nodenum-or-quotep-to-put-in).
;; nodenum-or-quotep-to-put-in may now always be a nodenum?
(defund check-for-var-subst-literal (literal-nodenum dag-array dag-len)
  (declare (xargs :guard (and (natp literal-nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< literal-nodenum dag-len))))
  (let ((expr (aref1 'dag-array dag-array literal-nodenum)))
    ;; we seek an expr of the form (not <nodenum>)
    (if (not (and (call-of 'not expr)
                  (= 1 (len (dargs expr)))
                  (integerp (darg1 expr))))
        (mv nil nil nil nil) ;fail
      (let ((non-nil-expr (aref1 'dag-array dag-array (darg1 expr)))) ;;we seek a NON-NIL-EXPR of the form (equal <nodenum-of-var> <thing>) or vice-versa
        (if (not (and (call-of 'equal non-nil-expr)
                      (= 2 (len (dargs non-nil-expr)))))
            (mv nil nil nil nil) ;fail
          (find-var-and-expr-to-subst (darg1 non-nil-expr) (darg2 non-nil-expr) dag-array dag-len) ;this is what prevents loops
          )))))

;; searches through literal-nodenums for a (negated) equality involving a variable (recall that a literal can be safely assumed false when rewriting other literals)
;; requires that the variable is equated to some term not involving itself (to prevent loops)
;; if such a (negated) equality is found, it is used to substitute in all the other literals.  the literal representing the equality is then dropped, eliminating that variable from the DAG.
;; Returns (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;fixme could this ever transform a literal into a constant?
;fixme what if more than one var can be substituted away?
;doesn't change any existing nodes in the dag (just builds new ones)
(defund substitute-a-var (literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (nat-listp all-literal-nodenums)
                              (all-< all-literal-nodenums dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0
                                                         <-of-nth-when-all-<
                                                         check-for-var-subst-literal
                                                         find-var-and-expr-to-subst
                                                         nodenum-of-var-to-substp)
                                                        (natp
                                                         ;cons-nth-0-nth-1 cons-of-nth-and-nth-plus-1 ;todo: why do these cause mv-nths to show up in appropriate places?
                                                         ))))))
  (if (endp literal-nodenums)
      (mv (erp-nil) nil all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (b* ((literal-nodenum (first literal-nodenums))
         ((mv foundp var nodenum-of-var
              nodenum-or-quotep-to-put-in ;may now always be a nodenum?
              )
          (check-for-var-subst-literal literal-nodenum dag-array dag-len)))
      (if (not foundp)
          ;; Keep looking:
          (substitute-a-var (rest literal-nodenums) all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
        ;; Substitute:
        (b* ((- (and ;; print ;; (or (eq t print) (eq :verbose print))
                 (and print (cw "~%(Using ~x0 to replace ~x1 (~x2 -> ~x3).~%" literal-nodenum var nodenum-of-var nodenum-or-quotep-to-put-in))
                 ;; (progn$ (cw "~%(Substituting to replace ~x0 (node ~x1) with:~%" var nodenum-of-var)
                 ;;         (if (quotep nodenum-or-quotep-to-put-in) ;always false?
                 ;;             (cw "~x0" nodenum-or-quotep-to-put-in)
                 ;;           (if print
                 ;;               (print-dag-only-supporters 'dag-array dag-array nodenum-or-quotep-to-put-in)
                 ;;             (cw ":elided"))))
                 ))
             ((when (consp nodenum-or-quotep-to-put-in)) ;tests for quotep - always false?
              (prog2$ (er hard? 'substitute-a-var "Surprised to see a var equated to a constant") ;fixme print more..
                      (mv (erp-t) nil all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
             ((mv erp literal-nodenums ;fixme could these ever be quoteps?
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                  )
              (rebuild-literals-with-substitution (remove literal-nodenum all-literal-nodenums) ;remove the equality we used ;make use of the fact that the item appears only once?
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  nodenum-of-var
                                                  nodenum-or-quotep-to-put-in ;known to be a nodenum
                                                  ))
             ((when erp) (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
             (- (and print (cw " ~x0 literals left, dag len is ~x1)~%" (len literal-nodenums) dag-len))))
          (mv (erp-nil) t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))

;; not phrased as a equality since multiple copies of the found literal may be removed
(defthm len-of-mv-nth2-of-substitute-a-var
  (implies (and (mv-nth 1 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                (subsetp-equal literal-nodenums all-literal-nodenums))
           (< (len (mv-nth 2 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
              (len all-literal-nodenums)))
  :hints (("Goal" :in-theory (enable substitute-a-var))))

(local (in-theory (enable check-for-var-subst-literal))) ;for the def-dag-builder-theorems just below

(def-dag-builder-theorems
  (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
  (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp literal-nodenums)
         (all-< literal-nodenums dag-len)
         (nat-listp all-literal-nodenums)
         (all-< all-literal-nodenums dag-len)))

;; (defthm <=-of-mv-nth-4-of-substitute-a-var
;;   (implies (and (mv-nth 1 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
;;                 (subsetp-equal literal-nodenums all-literal-nodenums))
;;            (<= (mv-nth 4 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
;;                2147483646))
;;   :hints (("Goal" :in-theory (enable SUBSTITUTE-A-VAR))))

(defthm nat-listp-of-mv-nth-2-of-substitute-a-var
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
                (nat-listp literal-nodenums)
                (nat-listp all-literal-nodenums)
                (all-< literal-nodenums dag-len)
                (all-< all-literal-nodenums dag-len))
           (nat-listp (mv-nth 2 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))))
  :hints (("Goal" :in-theory (enable substitute-a-var))))

(defthm true-listp-of-mv-nth-2-of-substitute-a-var
  (implies (true-listp all-literal-nodenums)
           (true-listp (mv-nth 2 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable substitute-a-var))))

(defthm all-<-of-mv-nth-2-of-substitute-a-var
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
                (nat-listp literal-nodenums)
                (nat-listp all-literal-nodenums)
                (all-< literal-nodenums dag-len)
                (all-< all-literal-nodenums dag-len))
           (all-< (mv-nth 2 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                  (mv-nth 4 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))))
  :hints (("Goal" :in-theory (enable substitute-a-var))))

;move
(defthm not-<-of-+-1-of-maxelem
 (implies (and (all-< x y)
               (integerp y)
               (all-integerp x)
               (consp x))
          (not (< y (+ 1 (maxelem x)))))
 :hints (("Goal" :in-theory (enable all-< maxelem))))

(local
 (defthm all-integerp-when-nat-listp
  (implies (nat-listp x)
           (all-integerp x))))

(local
 (DEFTHM RATIONALP-WHEN-natp
   (IMPLIES (natp X) (RATIONALP X))))

;; Repeatedly get rid of vars by substitution.
;; Returns (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;; Doesn't change any nodes if prover-depth > 0.
(defund substitute-vars (literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth num changep-acc)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (natp prover-depth)
                              (natp num)
                              (booleanp changep-acc))
                  :measure (len literal-nodenums)))
  (b* (((mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (substitute-a-var literal-nodenums literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
       ((when erp) (mv erp changep-acc literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       )
    (if (or (not changep)
            (endp literal-nodenums) ;todo: think about this
            )
        ;; No more vars to susbt:
        (mv (erp-nil)
            changep-acc
            literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
      (b* (((mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (if (and (= 0 prover-depth)
                     (= 0 (mod num 100))) ;; crunching is less important now that we substitute first with lits that were just rebuilt
                ;; Crunch the dag:
                (b* ((- (cw "(Crunching: ..."))
                     ((mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums)
                      (crunch-dag-array2-with-indices 'dag-array dag-array dag-len 'dag-parent-array literal-nodenums))
                     ;; TODO: Prove that this can't happen.  Need to know that
                     ;; build-reduced-nodes maps all of the literal-nodenums to
                     ;; nodenums (not constants -- currently)
                     ((when (not (and (rational-listp literal-nodenums) ;todo: using nat-listp here didn't work
                                      (all-< literal-nodenums dag-len))))
                      (er hard? 'substitute-vars "Bad nodenum after crunching.")
                      (mv (erp-t) literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                     (- (cw "Done).~%")))
                  (mv (erp-nil) literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
              ;; No change:
              (mv (erp-nil) literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
           ((when erp) (mv erp changep-acc literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
        ;; At least one var was substituted away, so keep going
        (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth (+ 1 num) t)))))

;;;
;;; tuple elimination
;;;

(defund get-known-true-listp-vars (nodenums-to-assume-false dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp nodenums-to-assume-false)
                              (all-< nodenums-to-assume-false dag-len))))
  (if (endp nodenums-to-assume-false)
      nil
    (let* ((nodenum (car nodenums-to-assume-false))
           (not-expr (aref1 'dag-array dag-array nodenum)))
      (if (and (consp not-expr)
               (eq 'not (ffn-symb not-expr))
               (= 1 (len (dargs not-expr)))
               (not (consp (first (dargs not-expr)))))
          (let ((expr (aref1 'dag-array dag-array (first (dargs not-expr)))))
            (if (and (consp expr)
                     (eq 'true-listp (ffn-symb expr))
                     (= 1 (len (dargs expr)))
                     (not (consp (first (dargs expr)))))
                (let ((possible-var (aref1 'dag-array dag-array (first (dargs expr)))))
                  (if (not (consp possible-var)) ;check for variable
                      (cons possible-var (get-known-true-listp-vars (cdr nodenums-to-assume-false) dag-array dag-len))
                    (get-known-true-listp-vars (cdr nodenums-to-assume-false) dag-array dag-len)))
              (get-known-true-listp-vars (cdr nodenums-to-assume-false) dag-array dag-len)))
        (get-known-true-listp-vars (cdr nodenums-to-assume-false) dag-array dag-len)))))

(defthm symbol-listp-of-get-known-true-listp-vars
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp nodenums-to-assume-false)
                (all-< nodenums-to-assume-false dag-len))
           (symbol-listp (get-known-true-listp-vars nodenums-to-assume-false dag-array dag-len)))
  :hints (("Goal" :in-theory (e/d (get-known-true-listp-vars) (natp)))))

(defthm subsetp-equal-of-get-known-true-listp-vars
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp nodenums-to-assume-false)
                (all-< nodenums-to-assume-false dag-len))
           (subsetp-equal (get-known-true-listp-vars nodenums-to-assume-false dag-array dag-len)
                          (strip-cars (make-dag-variable-alist 'dag-array dag-array dag-len))))
  :hints (("Goal" :in-theory (e/d (get-known-true-listp-vars) (natp)))))

(defthm not-<-of-+-1-and-maxelem
  (implies (and (all-< items bound)
                (nat-listp items)
                (integerp bound)
                (consp items))
           (not (< bound (binary-+ '1 (maxelem items)))))
  :hints (("Goal" :in-theory (enable all-< maxelem))))

(defthm axe-treep-of-list-of-cons
  (equal (axe-treep (list 'cons x y))
         (and (axe-treep x)
              (axe-treep y)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthm bounded-axe-treep-of-list-of-cons
  (equal (bounded-axe-treep (list 'cons x y) bound)
         (and (bounded-axe-treep x bound)
              (bounded-axe-treep y bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-treep
                                     ALL-BOUNDED-AXE-TREEP))))

(defthm axe-treep-of-make-cons-nest
  (equal (axe-treep (make-cons-nest items))
         (all-axe-treep items))
  :hints (("Goal" :in-theory (e/d (make-cons-nest)
                                  (axe-treep)))))

(defthm bounded-axe-treep-of-make-cons-nest
  (equal (bounded-axe-treep (make-cons-nest items) bound)
         (all-bounded-axe-treep items bound))
  :hints (("Goal" :in-theory (e/d (make-cons-nest
                                   all-bounded-axe-treep)
                                  (bounded-axe-treep)))))

;because the var names are symbols
(defthm all-axe-treep-of-make-var-names-aux
  (all-axe-treep (make-var-names-aux base-symbol startnum endnum))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

;because the var names are symbols
(defthm all-bounded-axe-treep-of-make-var-names-aux
  (all-bounded-axe-treep (make-var-names-aux base-symbol startnum endnum) bound)
  :hints (("Goal" :in-theory (enable all-bounded-axe-treep make-var-names-aux))))

;move
(defthm subsetp-equal-of-intersection-equal
  (implies (or (subsetp-equal x z)
               (subsetp-equal y z))
           (subsetp-equal (intersection-equal x y) z)))

;fixme does the tuple really have to be true-list?  what if we know only a lower bound on the length?  could we still do elim?
;;returns (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;should we do one destructor or all of them?
;if we ever implement clause mitering, this will need to fix up the test-cases, because it changes the vars in the dag..
;;smashes the appropriate translation-array and 'tag-array (does it still?)
;doesn't change any existing nodes in the dag (just builds new ones)
(defund eliminate-a-tuple (literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (consp literal-nodenums)
                              (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len)))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0
                                                           <-of-nth-when-all-<
                                                           FIND-VAR-AND-EXPR-TO-SUBST
                                                           NODENUM-OF-VAR-TO-SUBSTP
                                                           natp-of-lookup-equal-when-dag-variable-alistp
                                                           natp-of-cdr-of-assoc-equal-when-dag-variable-alistp)
                                                        (natp))))))
  (let* ((true-listp-vars (get-known-true-listp-vars literal-nodenums dag-array dag-len))
         (var-length-alist (get-var-length-alist-for-tuple-elimination literal-nodenums dag-array dag-len nil))
         (vars-given-lengths (strip-cars var-length-alist))
         (true-listp-vars-given-lengths (intersection-eq true-listp-vars vars-given-lengths))
;fixme do we need this check for soundness?  as long as we know the length of the var and that it is a true-listp, replacing it with a cons nest should be sound, right?  maybe we don't want to do it if there are array ops?
         (var-to-elim (var-okay-to-elim true-listp-vars-given-lengths dag-array dag-len dag-variable-alist literal-nodenums))
         )
    (if (not var-to-elim)
        (mv (erp-nil) nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
      (b* ((var var-to-elim) ;fixme
           (res (assoc-eq var dag-variable-alist))
           ((when (not res)) ;todo: strengthen guard and prove that this cannot happen
            (mv :var-not-in-dag-variable-alist nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
           (nodenum-of-var (cdr res)))
        (progn$ (cw "(Eliminating destructors for variable ~x0." var)
                (and (eq :verbose print) (cw "literals: ~x0~%" literal-nodenums))
                (and (eq :verbose print) (print-dag-only-supporters-lst literal-nodenums 'dag-array dag-array))
                (let* ((len-of-var (lookup-eq var var-length-alist))
                       (dag-vars (vars-that-support-dag-nodes literal-nodenums 'dag-array dag-array dag-len))
                       (new-vars (make-var-names-aux (pack$ var '-) 0 (+ -1 len-of-var))) ;ffixme call a no-clash version?
                       )
                  (if (intersection-eq new-vars dag-vars)
                      (progn$ (cw "new vars: ~x0dag vars: ~x1.~%" new-vars dag-vars)
                              (er hard? 'eliminate-a-tuple "variable clash") ;fffixme handle this better
                              (mv (erp-t) nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    (b* ((cons-nest (make-cons-nest new-vars)) ;inefficient to build this first as a term and then merge into dag?
                         ((mv erp cons-nest-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                          ;; TODO: Call something simpler here (could also take advantage of the fact that the entire term, even the vars, is new to the dag):
                          (merge-term-into-dag-array-basic cons-nest
                                                            nil ;no var replacement
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            'dag-array 'dag-parent-array
                                                            nil ;; no interpreted functions
                                                            ))
                         ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ;; TODO: Prove this can't happen and drop this check
                         ((when (consp cons-nest-nodenum)) ;check for a quoted constant
                          (mv :unexpected-result nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ((mv erp literal-nodenums ;fixme could these ever be quoteps? if so, call handle-constant-disjuncts and return provedp?
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                          ;; ;this puts in the cons nest for the var everywhere it appears (fixme i guess nth of cons will then fire a lot..)
                          ;; this used to be accomplished by rewriting - yuck
                          (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              nodenum-of-var cons-nest-nodenum))
                         ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         (- (cw ")~%")))
                      (mv (erp-nil)
                          t ;; changep is true
                          literal-nodenums
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          ;;(split-test-cases test-cases var new-vars) ;slow?
                          )))))))))

;; ;fixme change this to do less consing in the usual case of an objectcive of ?

;; ;fixme think about get-result vs. get-result-expandable
;; ;returns a nodenum-or-quotep, or nil
;; (defmacro get-result (nodenum rewrite-objective result-array)
;;   `(lookup-eq ,rewrite-objective (aref1 'result-array ,result-array ,nodenum)))

;; ;returns a nodenum-or-quotep, or nil
;; (defmacro get-result-expandable (nodenum rewrite-objective result-array)
;;   `(lookup-eq ,rewrite-objective (aref1-expandable 'result-array ,result-array ,nodenum)))

;; (defmacro set-result (nodenum rewrite-objective result result-array)
;;   `(aset1-expandable 'result-array ,result-array ,nodenum (acons-fast ,rewrite-objective ,result (aref1-expandable 'result-array ,result-array ,nodenum))))

;put dag in the name
;fixme whitespace and after last node isn't quite right
;does this do the right thing for very small arrays?
;ffixme allow the key node to be not the top node?
(defund print-negated-literal (nodenum dag-array-name dag-array dag-len)
  (declare (type (integer 0 *) nodenum)
           (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp nodenum)
                              (< nodenum dag-len)
                              (symbolp dag-array-name))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))
           (ignore dag-len))
  (let* ((expr (aref1 dag-array-name dag-array nodenum))
         (call-of-notp (and (consp expr)
                            (eq 'not (ffn-symb expr))
                            (= 1 (len (dargs expr)))
                            (integerp (darg1 expr))))
         (top-node-to-print (if call-of-notp (darg1 expr) nodenum))
         )
    (progn$
     ;;print the open paren:
     (cw "(")
     ;; We print XXX where there would usually be a node number because the
     ;; negation does not actually have a node.
     (and (not call-of-notp) (cw "(xxx NOT ~x0)~% " top-node-to-print))
     ;;print the elements
     (print-supporting-dag-nodes top-node-to-print 0 dag-array-name dag-array (list top-node-to-print) t)
     ;;print the close paren:
     (cw ")~%"))))

;recall that the case is the negation of all the literals
;fixme similar name to print-negated-literal-list
(defund print-axe-prover-case (literal-nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-natp literal-nodenums)
                              (true-listp literal-nodenums)
                              (all-< literal-nodenums dag-len))))
  (if (endp literal-nodenums)
      nil
    (progn$ (print-negated-literal (first literal-nodenums) dag-array-name dag-array dag-len)
            (cw "~%")
            (print-axe-prover-case (rest literal-nodenums) dag-array-name dag-array dag-len))))

(defthm <-of-+-1-of-maxelem
  (implies (and (all-< lst x)
                (all-integerp lst)
                (integerp x)
                (consp lst))
           (not (< x (+ 1 (MAXELEM lst)))))
  :hints (("Goal" :in-theory (enable maxelem all-<))))

;; Returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
;why is this separate?
(defund simplify-var-and-add-to-dag-for-axe-prover (tree equiv
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        rule-alist
                                                        nodenums-to-assume-false
                                                        equiv-alist print
                                                        info tries interpreted-function-alist monitored-symbols
                                                        ;; embedded-dag-depth
                                                        case-designator work-hard-when-instructedp prover-depth)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbolp equiv)
                              (symbolp tree)
                              (<= dag-len 2147483645)
                              (all-natp nodenums-to-assume-false)
                              (true-listp nodenums-to-assume-false)
                              (all-< nodenums-to-assume-false dag-len)))
           (ignore rule-alist equiv-alist interpreted-function-alist monitored-symbols
                   ;;embedded-dag-depth
                   case-designator work-hard-when-instructedp
                   prover-depth ;fixme
                   ))
  (prog2$ nil ;;(cw "Rewriting the variable ~x0" tree) ;new!
          ;; It's a variable:  FFIXME perhaps add it first and then use assumptions?
          ;; First try looking it up in the assumptions (fixme make special version of replace-term-using-assumptions-for-axe-prover for a variable?):
          (let ((assumption-match (replace-term-using-assumptions-for-axe-prover tree equiv nodenums-to-assume-false dag-array print)))
            (if assumption-match
                ;; We replace the variable with something it's equated to in nodenums-to-assume-false.
                ;; We don't rewrite the result (by the second pass, nodenums-to-assume-false will be simplified - and maybe we should always do that?)
     ;fixme what if there is a chain of equalities to follow?
                (mv (erp-nil) assumption-match dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
              ;; no match, so we just add the variable to the DAG:
              ;;make this a macro? this one might be rare..  same for other adding to dag operations?
              (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist) ;fixme simplify nodenum?
                (add-variable-to-dag-array tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))

;; This duplicates the term x, but if it's  the variable COUNT, that's ok.
(defmacro zp-fast (x)
  `(mbe :logic (zp ,x)
        :exec (= 0 ,x)))

;; see also translate-args
(defun lookup-args-in-result-array (args result-array-name result-array)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              (array1p result-array-name result-array)
                              (< (largest-non-quotep args) (alen1 result-array-name result-array)))))
  (if (endp args)
      nil
    (let ((arg (car args)))
      (if (consp arg) ;check for quotep
          (cons arg
                (lookup-args-in-result-array (cdr args) result-array-name result-array))
        (cons (aref1 result-array-name result-array arg)
              (lookup-args-in-result-array (cdr args) result-array-name result-array))))))

(defund axe-prover-optionsp (options)
  (declare (xargs :guard t))
  (and (alistp options)
       (subsetp-eq (strip-cars options) '(:no-stp))))

;todo
