; DAGs, represented as lists
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

;; This books contains notions related to DAGs represented as alists.  See also
;; dag-arrays.lisp.

(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/pairlis-dollar-fast" :dir :system)
;(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/utilities/printing" :dir :system) ;for print-list
(include-book "kestrel/acl2-arrays/bounded-nat-alists" :dir :system)
(include-book "numeric-lists")
(include-book "bounded-dag-exprs")
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "keep-atoms")
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/utilities/lists/add-to-set-theorems" :dir :system))
(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))

(local (in-theory (disable symbol-alistp strip-cdrs alistp))) ;prevent inductions

(defthm all-myquotep-forward-to-all-consp
  (implies (all-myquotep x)
           (all-consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ALL-MYQUOTEP all-consp))))

;rename
(defthmd alistp-guard-hack
  (implies (and (alistp dag)
                (not (consp (nth 0 dag))))
           (not (nth 0 dag)))
  :hints (("Goal" :in-theory (enable alistp))))

(defthm dargp-less-than-of-cdr-of-assoc-equal
  (implies (and (all-dargp-less-than (strip-cdrs alist) bound)
                (assoc-equal term alist))
           (dargp-less-than (cdr (assoc-equal term alist))
                                       bound))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defun top-nodenum (dag)
  (declare (xargs :GUARD (ALISTP dag) ;or require weak-dagp?  at least require non-empty?
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))
                  ))
  (if (endp dag)
      -1
    (let* ((entry (car dag))
           (nodenum (car entry)))
      nodenum)))

;;
;; definition of DAGs
;;

;;
;; weak-dagp
;;

;; Checks that DAG is a true-list of dag "entries" (TODO: name that notion?).
(defun weak-dagp-aux (dag)
  (declare (xargs :guard t))
  (if (atom dag)
      (null dag)
    (let ((entry (car dag)))
      (and (consp entry)
           (let* ((nodenum (car entry))
                  (expr (cdr entry)))
                (and (natp nodenum)
                     (bounded-dag-exprp nodenum expr)
                     (weak-dagp-aux (cdr dag))))))))

(defthm symbolp-of-cdar-when-weak-dagp-aux-cheap
  (implies (and (weak-dagp-aux dag)
                (consp dag)
                (not (consp (cdr (car dag)))))
           (symbolp (cdr (car dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux bounded-dag-exprp))))

(defthm rational-listp-of-strip-cars-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (rational-listp (strip-cars dag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm weak-dagp-aux-of-cdr
  (implies (weak-dagp-aux dag)
           (weak-dagp-aux (cdr dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm weak-dagp-aux-forward-to-alistp
  (implies (weak-dagp-aux dag)
           (alistp dag))
  :rule-classes :forward-chaining)

(defthm integerp-of-car-of-car-when-weak-dagp-aux-cheap
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (integerp (car (car dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

;even holds for bad nodenums or nodenums of vars, since the cdr will return nil
(defthm true-listp-of-dargs-of-lookup-equal-when-weak-dagp-aux-cheap
  (implies (weak-dagp-aux dag)
           (true-listp (dargs (lookup-equal nodenum dag))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0 dargs))))

(defthm all-dargp-less-than-of-dargs-of-lookup-equal
  (implies (and (weak-dagp-aux dag)
                (natp nodenum)
                (natp nodenum2)
                (<= nodenum nodenum2)
                (consp (lookup-equal nodenum dag))
                (not (equal (car (lookup-equal nodenum dag))
                            'quote)))
           (all-dargp-less-than (dargs (lookup-equal nodenum dag)) nodenum2))
  :hints (("Goal" :expand ((ASSOC-EQUAL NODENUM DAG)
                           (LOOKUP-EQUAL NODENUM DAG)
                           (LOOKUP-EQUAL NODENUM (CDR DAG)))
           :in-theory (enable bounded-dag-exprp
                              dag-exprp0))))

(defthm dag-exprp0-of-lookup-equal-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (lookup-equal n dag))
           (dag-exprp0 (lookup-equal n dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux lookup-equal))))

(defthm natp-of-maxelem-of-strip-cars-when-rev-dagp
  (implies (and (weak-dagp-aux rev-dag)
                (consp rev-dag))
           (natp (maxelem (strip-cars rev-dag))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable weak-dagp-aux strip-cars))))

(defthm weak-dagp-aux-of-append
  (equal (weak-dagp-aux (append x y))
         (and (weak-dagp-aux (true-list-fix x))
              (weak-dagp-aux y)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm weak-dagp-aux-of-reverse-list
  (equal (weak-dagp-aux (reverse-list dag))
         (weak-dagp-aux (true-list-fix dag)))
  :hints (("Goal" :in-theory (enable reverse-list))))

;this does enforce that children are less than the parents
;does not enforce that all the nodes come in order!
;does not enforce that child nodes exist!
;does not enforce that each node appears only once
;does not enforce that there are no gaps in the node numbering
;does not enforce that function calls in dag exprs have the right arity
(defund weak-dagp (dag)
  (declare (xargs :guard t))
  (and ;(true-listp dag)
       (consp dag) ;a dag can't be empty (but often we have items that are either dags or quoted constants)
       (weak-dagp-aux dag)))

(defthm weak-dagp-of-cdr
  (implies (weak-dagp dag)
           (equal (weak-dagp (cdr dag))
                  (consp (cdr dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

;keeping this disabled for now, since it could be expensive.
(defthmd alistp-when-weak-dagp
  (implies (weak-dagp dag)
           (alistp dag)))

(defthm weak-dagp-forward-to-alistp
  (implies (weak-dagp dag)
           (alistp dag))
  :rule-classes :forward-chaining)

(defthm weak-dagp-forward-to-natp-of-car-of-car
  (implies (weak-dagp dag)
           (natp (car (car dag))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm weak-dagp-of-reverse-list
  (equal (weak-dagp (reverse-list dag))
         (weak-dagp (true-list-fix dag)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm integerp-of-car-of-car-when-weak-dagp-cheap
  (implies (and (weak-dagp dag)
                (consp dag))
           (integerp (car (car dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm true-listp-of-dargs-of-lookup-equal-when-weak-dagp-cheap
  (implies (weak-dagp dag)
           (true-listp (dargs (lookup-equal nodenum dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm all-dargp-less-than-of-dargs-of-lookup-equal-when-weak-dagp
  (implies (and (weak-dagp dag)
                (natp nodenum)
                (natp nodenum2)
                (<= nodenum nodenum2)
                (consp (lookup-equal nodenum dag))
                (not (equal (car (lookup-equal nodenum dag))
                            'quote)))
           (all-dargp-less-than (dargs (lookup-equal nodenum dag)) nodenum2))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm dag-exprp0-of-lookup-equal-when-weak-dagp
  (implies (and (weak-dagp dag)
                (lookup-equal n dag))
           (dag-exprp0 (lookup-equal n dag)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

;;
;; pseudo-dagp
;;

; current-nodenum should be the top nodenum of dag.  it counts down to -1, in which case the dag should be nil.
(defund pseudo-dagp-aux (dag current-nodenum)
  (declare (type (integer -1 *) current-nodenum))
  (if (< current-nodenum 0)
      (null dag)
    (and (consp dag)
         (let ((entry (first dag)))
           (and (consp entry)
                (let ((nodenum (car entry))
                      (expr (cdr entry)))
                  (and (eql nodenum current-nodenum)
                       (bounded-dag-exprp current-nodenum expr)
                       (pseudo-dagp-aux (rest dag) (+ -1 current-nodenum)))))))))

(defthm true-listp-when-pseudo-dagp-aux
  (implies (pseudo-dagp-aux dag-lst current-nodenum)
           (true-listp dag-lst))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm alistp-when-pseudo-dagp-aux
  (implies (pseudo-dagp-aux dag-lst current-nodenum)
           (alistp dag-lst))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-cdr
  (implies (and (pseudo-dagp-aux dag (+ 1 n))
                (integerp n))
           (pseudo-dagp-aux (cdr dag) n))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp-aux) (bounded-dag-exprp)))))

(defthm pseudo-dagp-aux-when-not-consp-cheap
  (implies (not (consp dag))
           (equal (pseudo-dagp-aux dag n)
                  (and (null dag)
                       (< n 0))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm dag-exprp-of-lookup-equal-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (<= n current-nodenum)
                (natp n)
                (integerp current-nodenum))
           (bounded-dag-exprp n (lookup-equal n dag)))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp-aux LOOKUP-EQUAL assoc-equal)
                                  (bounded-dag-exprp)))))

(defthm pseudo-dagp-aux-forward
  (implies (and (pseudo-dagp-aux dag n)
                (integerp n)
                (consp dag))
           (<= 0 n))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;; Checks that the node numbering is correct with no gaps and that nodes only
;; refer to smaller nodes.  Does not check that the arities of the functions
;; are correct (so this is kind of like pseudo-termp).  This is not a good
;; function to use as a guard when recurring down dags because you want to go
;; until nil is reached, but nil is not a pseudo-dag.  Instead, see
;; weak-dagp-aux or pseudo-dagp-aux.
(defund pseudo-dagp (dag)
  (declare (xargs :guard t))
  (and (consp dag) ;a dag can't be empty (but often we have items that are either dags or quoted constants)
       (let ((first-entry (first dag)))
         (and (consp first-entry)
              (let ((top-nodenum (car first-entry)))
                (and (natp top-nodenum)
                     (pseudo-dagp-aux dag top-nodenum)))))))

;keeping this disabled for now, since it could be expensive.
(defthmd alistp-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (alistp dag))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

;keeping this disabled for now, since it could be expensive.
(defthmd true-listp-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (true-listp dag)))

(defthm pseudo-dagp-forward-to-true-listp
  (implies (pseudo-dagp dag)
           (true-listp dag))
  :rule-classes :forward-chaining)

(defthm pseudo-dagp-forward-to-natp-of-caar
  (implies (pseudo-dagp dag)
           (natp (car (car dag))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm pseudo-dagp-forward-to-posp-of-len
  (implies (pseudo-dagp dag)
           (posp (len dag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm dag-exprp-of-lookup-equal-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (<= n (top-nodenum dag))
                (natp n))
           (bounded-dag-exprp n (lookup-equal n dag)))
  :hints (("Goal" :in-theory (e/d (PSEUDO-DAGP) (bounded-dag-exprp)))))

(defthmd pseudo-dagp-rewrite
  (equal (pseudo-dagp dag)
         (and (consp dag)
              (natp (top-nodenum dag))
              (pseudo-dagp-aux dag (top-nodenum dag))))
  :hints (("Goal" :expand (pseudo-dagp-aux dag nil)
           :in-theory (enable pseudo-dagp))))

;(pseudo-dagp '((2 foo '77 1) (1 bar 0) (0 . x)))

(defthm weak-dagp-aux-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (integerp nodenum))
           (weak-dagp-aux dag))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX WEAK-DAGP-AUX))))

(defthm weak-dagp-aux-when-pseudo-dagp-aux-2
  (implies (and (pseudo-dagp-aux dag (top-nodenum dag))
                (natp (top-nodenum dag)))
           (weak-dagp-aux dag)))

(defthm weak-dagp-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (natp nodenum))
           (weak-dagp dag))
  :hints (("Goal" :in-theory (enable weak-dagp pseudo-dagp-aux weak-dagp-aux))))

;; Pseudo-dagp is a stronger check
(defthm weak-dagp-when-pseudo-dagp
  (implies (pseudo-dagp x)
           (weak-dagp x))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defun pseudo-dag-or-quotep (obj)
  (declare (xargs :guard t))
  (or (pseudo-dagp obj)
      (myquotep obj)))

;;;
;;; find-node-for-expr
;;;

;; Looks for the node in DAG whose expression is EXPR.
;returns nil or the nodenum
;like assoc but looks for a given value (second component of an entry), rather than a given key
;; More efficient lookups are possible using indices like the parent-array.
;; See also find-node-for-expr2.
(defun find-node-for-expr (expr dag)
  (declare (xargs :guard (alistp dag)
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))
                  ))
  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (expr2 (cdr entry)))
      (if (equal expr expr2)
          (car entry)
        (find-node-for-expr expr (cdr dag))))))

(defthm find-node-for-expr-type
  (implies (weak-dagp-aux dag)
           (or (natp (find-node-for-expr expr dag))
               (equal (find-node-for-expr expr dag) nil)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm find-node-for-expr-bound-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux main-dag (top-nodenum main-dag))
                (find-node-for-expr expr main-dag))
           (<= (find-node-for-expr expr main-dag)
               (car (car main-dag))))
  :rule-classes (:rewrite (:linear :trigger-terms ((find-node-for-expr expr main-dag))))
  :hints (("Goal" :expand ((pseudo-dagp-aux main-dag (car (car main-dag)))
                           (pseudo-dagp-aux (cdr main-dag)
                                            (car (cadr main-dag)))
                           (pseudo-dagp-aux (cdr main-dag)
                                            (+ -1 (car (car main-dag))))))))

;;;
;;; find-node-for-expr2-aux
;;;

;returns nil or the nodenum
;like assoc but looks for a given value (second component of an entry), rather than a given key
(defun find-node-for-expr2-aux (expr dag node-to-stop-checking)
  (declare (xargs :guard (weak-dagp-aux dag)
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack))))
           (type integer node-to-stop-checking)
           )
  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (nodenum (car entry)))
      (if (<= nodenum node-to-stop-checking)
          nil
        (let ((expr2 (cdr entry)))
          (if (equal expr expr2)
              nodenum
            (find-node-for-expr2-aux expr (cdr dag) node-to-stop-checking)))))))

(defthm find-node-for-expr2-aux-type
  (implies (weak-dagp-aux dag)
           (or (natp (find-node-for-expr2-aux expr dag stop-node))
               (equal (find-node-for-expr2-aux expr dag stop-node) nil)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm integerp-of-find-node-for-expr2-aux
  (implies (and (weak-dagp-aux dag)
                (find-node-for-expr2-aux expr dag stop-node))
           (integerp (find-node-for-expr2-aux expr dag stop-node)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm find-node-for-expr2-aux-bound-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux main-dag (top-nodenum main-dag))
                (find-node-for-expr2-aux expr main-dag stop-node))
           (<= (find-node-for-expr2-aux expr main-dag stop-node)
               (car (car main-dag))))
  :rule-classes (:rewrite (:linear :trigger-terms ((find-node-for-expr2-aux expr main-dag stop-node))))
  :hints (("Goal" :expand ((pseudo-dagp-aux main-dag (car (car main-dag)))
                           (pseudo-dagp-aux (cdr main-dag)
                                            (car (cadr main-dag)))
                           (pseudo-dagp-aux (cdr main-dag)
                                            (+ -1 (car (car main-dag))))))))

;;;
;;; find-node-for-expr2
;;;

;this version uses the dag ordering property to stop looking when it finds a
;node whose nodenum is smaller than the largest argument (if any) of target
;expr
; returns nil or the nodenum like assoc but looks for a given value
;(second component of an entry), rather than a given key
(defund find-node-for-expr2 (expr dag)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (dag-exprp0 expr))
                  :guard-hints (("Goal" :in-theory (enable largest-non-quotep)))))
  (if (or (variablep expr)
          (fquotep expr))
      (find-node-for-expr expr dag)
    ;;otherwise, it's a function call and we can make an optimization
    (let* ((largest-nodenum-arg (largest-non-quotep (dargs expr)))) ;may be -1
      (find-node-for-expr2-aux expr dag largest-nodenum-arg))))

(defthm find-node-for-expr2-type
  (implies (weak-dagp-aux dag)
           (or (natp (find-node-for-expr2 expr dag))
               (equal (find-node-for-expr2 expr dag) nil)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable find-node-for-expr2))))

(defthm integerp-of-find-node-for-expr2
  (implies (and (weak-dagp-aux dag)
                (find-node-for-expr2 expr dag))
           (integerp (find-node-for-expr2 expr dag)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm nonneg-of-find-node-for-expr2
  (implies (and (weak-dagp-aux dag)
                (find-node-for-expr2 expr dag))
           (<= 0 (find-node-for-expr2 expr dag))))

(defthm find-node-for-expr2-bound-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux main-dag (top-nodenum main-dag))
                (find-node-for-expr2 expr main-dag))
           (<= (find-node-for-expr2 expr main-dag)
               (car (car main-dag))))
  :rule-classes (:rewrite (:linear :trigger-terms ((find-node-for-expr2 expr main-dag))))
  :hints (("Goal" :in-theory (enable find-node-for-expr2))))

(defthm find-node-for-expr2-of-nil
  (equal (find-node-for-expr2 expr nil)
         nil)
  :hints (("Goal" :in-theory (enable FIND-NODE-FOR-EXPR2))))

;deprecate? or keep as the simple, logical story?  used once in the lifter...
;EXPR must be an expr that can appear in a DAG node (so no nested function calls, etc.): a function call applied to nodenums/quoteps, or a quotep, or a variable
;returns (mv nodenum new-dag) where nodenum is the (not-necessarily new) node in new-dag which represents EXPR
;fixme allow this to return a constant instead of a nodenum? or perhaps this is never called with expr being a constant. perhaps split this depending on whether we are adding a var or a function call
(defund add-to-dag (expr dag)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (dag-exprp0 expr))
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))))
  (let* ((node-if-present (find-node-for-expr2 ;find-node-for-expr
                           expr dag)))
    (if node-if-present
        (mv node-if-present dag)
      (let ((new-node-num (+ 1 (top-nodenum dag))))
        (mv new-node-num
            (acons new-node-num
                   expr
                   dag))))))

(defthm natp-of-mv-nth-0-of-add-to-dag
  (implies (weak-dagp-aux dag)
           (natp (mv-nth 0 (add-to-dag expr dag))))
  :hints (("Goal" :in-theory (e/d (add-to-dag) ()))))

(defthm weak-dagp-aux-of-mv-nth-1-of-add-to-dag
  (implies (and (weak-dagp-aux dag)
                (bounded-dag-exprp (+ 1 (top-nodenum dag)) expr))
           (weak-dagp-aux (mv-nth 1 (add-to-dag expr dag))))
  :hints (("Goal" :in-theory (enable add-to-dag acons (:d weak-dagp-aux) BOUNDED-DAG-EXPRP DAG-EXPRP0))))

(defthm pseudo-dagp-aux-of-mv-nth-1-of-add-to-dag
  (implies (and (pseudo-dagp dag)
                (bounded-dag-exprp (+ 1 (top-nodenum dag)) expr))
           (pseudo-dagp-aux (mv-nth 1 (add-to-dag expr dag))
                            (top-nodenum (mv-nth 1 (add-to-dag expr dag)))))
  :hints (("Goal" :expand ((PSEUDO-DAGP-AUX DAG (CAR (CAR DAG)))
                           (PSEUDO-DAGP-AUX DAG 0)
                           (PSEUDO-DAGP-AUX (ACONS (+ 1 (CAR (CAR DAG))) EXPR DAG)
                                            (+ 1 (CAR (CAR DAG)))))
           :in-theory (enable add-to-dag PSEUDO-DAGP))))

(defthm pseudo-dagp-of-mv-nth-1-of-add-to-dag
  (implies (and (pseudo-dagp dag)
                (bounded-dag-exprp (+ 1 (top-nodenum dag)) expr))
           (pseudo-dagp (mv-nth 1 (add-to-dag expr dag))))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp  add-to-dag)
                                  (pseudo-dagp-aux-of-mv-nth-1-of-add-to-dag
                                   bounded-dag-exprp))
           :use (:instance pseudo-dagp-aux-of-mv-nth-1-of-add-to-dag))))

(defthm weak-dagp-aux-of-mv-nth-1-of-add-to-dag-alt
  (implies (and (weak-dagp-aux dag)
                (consp dag)
                (bounded-dag-exprp (+ 1 (car (car dag))) expr))
           (weak-dagp-aux (mv-nth 1 (add-to-dag expr dag))))
  :hints (("Goal" :in-theory (enable add-to-dag))))

(defthm add-to-dag-bound
  (implies (pseudo-dagp dag)
           (< (mv-nth 0 (add-to-dag term dag))
              (+ 1 (top-nodenum (mv-nth 1 (add-to-dag term dag))))))
  :hints (("Goal" :in-theory (enable add-to-dag pseudo-dagp))))

(defthm add-to-dag-bound3
  (<= (top-nodenum dag)
      (top-nodenum (mv-nth 1 (add-to-dag term dag))))
  :rule-classes ((:linear :trigger-terms ((top-nodenum (mv-nth 1 (add-to-dag term dag))))))
  :hints (("Goal" :in-theory (enable add-to-dag pseudo-dagp))))

(defthm add-to-dag-bound2
  (implies (pseudo-dagp dag)
           (dargp-less-than (mv-nth 0 (add-to-dag expr dag))
                                       (+ 1 (top-nodenum (mv-nth 1 (add-to-dag expr dag))))))
  :hints (("Goal" :in-theory (e/d (add-to-dag pseudo-dagp dargp-less-than) ()))))

(defthm  add-to-dag-of-nil
  (equal (add-to-dag expr nil)
         (mv 0 (acons 0 expr nil)))
  :hints (("Goal" :in-theory (enable add-to-dag))))

(defthm consp-of-mv-nth-1-of-add-to-dag
  (consp (mv-nth 1 (add-to-dag expr dag)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-to-dag find-node-for-expr2))))

;;
;; dag-vars
;;

(defun dag-vars-aux (dag acc)
  (declare (xargs :guard (alistp dag)))
  (if (endp dag)
      acc
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (dag-vars-aux (cdr dag)
                    (if (variablep expr)
                        (cons expr acc) ;could do add-to-set-eq, but there should be no duplicates, i guess
                      acc)))))

(defthm symbol-listp-of-dag-vars-aux
  (implies (and (symbol-listp acc)
                (weak-dagp dag))
           (symbol-listp (dag-vars-aux dag acc)))
  :hints (("Goal" :in-theory (enable weak-dagp dag-exprp0))))

(defund dag-vars (dag)
  (declare (xargs :guard (or (quotep dag)
                             (alistp dag))))
  (if (quotep dag)
      nil
    (dag-vars-aux dag nil)))

(defthm symbol-listp-of-dag-vars
  (implies (weak-dagp dag)
           (symbol-listp (dag-vars dag)))
  :hints (("Goal" :in-theory (enable dag-vars))))

(defun get-vars-from-dags-aux (dags acc)
  (if (endp dags)
      acc
    (let* ((dag (first dags))
           (vars (dag-vars dag)))
      (get-vars-from-dags-aux (rest dags) (union-eq vars acc)))))

(defun get-vars-from-dags (dags)
  (get-vars-from-dags-aux dags nil))

;;
;; dag-fns
;;

(defun dag-fns-aux (dag acc)
  (declare (xargs :guard (and (true-listp dag)
                              (weak-dagp-aux dag)
                              (symbol-listp acc))
                  :guard-hints (("Goal" :in-theory (enable dag-exprp0)))))
  (if (endp dag)
      acc
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (and (consp expr)
               (not (eq 'quote (car expr))))
          (dag-fns-aux (cdr dag) (add-to-set-eq (car expr) acc))
        (dag-fns-aux (cdr dag) acc)))))

(defthm symbol-listp-of-dag-fns-aux
  (implies (and (symbol-listp acc)
                (weak-dagp dag))
           (symbol-listp (dag-fns-aux dag acc)))
  :hints (("Goal" :in-theory (enable weak-dagp dag-exprp0))))

;dag is a dag-lst or quotep
(defund dag-fns (dag)
  (declare (xargs :guard (or (quotep dag)
                             (weak-dagp dag))))
  (if (quotep dag)
      nil
    (merge-sort-symbol-< (dag-fns-aux dag nil))))

(defthm symbol-listp-of-dag-fns
  (implies (weak-dagp dag)
           (symbol-listp (dag-fns dag)))
  :hints (("Goal" :in-theory (enable dag-fns))))

;could allow the result to have duplicate nodes, but it doesn't seem worth it to check for that, if we are going to simplify the result anyway
;may be slow
(mutual-recursion
 ;;returns (mv nodenum-or-quotep new-dag)
 ;todo: reorder params
 (defun compose-term-and-dag-aux (term
                                  var-replacement-alist ;maps vars in the term to nodenums/quoteps
                                  dag)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-alistp var-replacement-alist)
                               (pseudo-dagp dag)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag))))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       (let ((match (assoc-eq term var-replacement-alist)))
         (if match
             ;; return the nodenum or quotep to which the var is mapped
             (mv (cdr match) dag)
           (add-to-dag term dag)))
     (if (fquotep term)
         (mv term dag)
       ;;must be a function call
       (let* ((fn (ffn-symb term))
              (args (fargs term)))
         (mv-let (args-nodenums-and-constants dag)
           (compose-term-and-dag-aux-lst args var-replacement-alist dag)
           (if (symbolp fn)
               (add-to-dag (cons fn args-nodenums-and-constants)
                           dag)
             ;;it's a lambda.  Recur on the body and use an alist that maps
             ;;formals to the nodenums/constants of the corresponding args
             (compose-term-and-dag-aux (lambda-body fn)
                                       (pairlis$-fast (lambda-formals fn) args-nodenums-and-constants)
                                       dag)))))))

 ;;returns (mv nodenums-and-constants dag)
 (defun compose-term-and-dag-aux-lst (terms var-replacement-alist dag)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp var-replacement-alist)
                               (pseudo-dagp dag)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag))))))
   (if (endp terms)
       (mv nil dag)
     (mv-let (car-nodenum dag)
       (compose-term-and-dag-aux (car terms) var-replacement-alist dag)
       (mv-let (cdr-nodenums dag)
         (compose-term-and-dag-aux-lst (cdr terms) var-replacement-alist dag)
         (mv (cons car-nodenum cdr-nodenums)
             dag))))))

(make-flag compose-term-and-dag-aux)

(defthm-flag-compose-term-and-dag-aux
  (defthm true-listp-of-mv-nth-0-of-compose-term-and-dag-aux
    t ;don't need to know anything about the non-list case
    :rule-classes nil
    :flag compose-term-and-dag-aux)
  (defthm true-listp-of-mv-nth-0-of-compose-term-and-dag-aux-lst
    (true-listp (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
    :flag compose-term-and-dag-aux-lst))

(defthm-flag-compose-term-and-dag-aux
  ;should be allowed to omit this?
  (defthm dummy1
    t ;don't need to know anything about the non-list case
    :rule-classes nil
    :flag compose-term-and-dag-aux)
  (defthm len-of-mv-nth-0-of-compose-term-and-dag-aux-lst
    (equal (len (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
           (len terms))
    :flag compose-term-and-dag-aux-lst))

(defthm-flag-compose-term-and-dag-aux
  ;should be allowed to omit this?
  (defthm dummy2
    t ;don't need to know anything about the non-list case
    :rule-classes nil
    :flag compose-term-and-dag-aux)
  (defthm consp-of-mv-nth-0-of-compose-term-and-dag-aux-lst
    (equal (consp (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
           (consp terms))
    :flag compose-term-and-dag-aux-lst))

;; (defthm-flag-compose-term-and-dag-aux
;;   (defthm dargp-of-mv-nth-0-of-compose-term-and-dag-aux
;;     (implies (weak-dagp-aux dag)
;;              (dargp (mv-nth 0 (compose-term-and-dag-aux term var-replacement-alist dag))))
;;     :flag compose-term-and-dag-aux)
;;   (defthm all-dargp-of-mv-nth-0-of-compose-term-and-dag-aux-lst
;;     (implies (weak-dagp-aux dag)
;;              (all-dargp (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag))))
;;     :flag compose-term-and-dag-aux-lst))

;rename
(defthm-flag-compose-term-and-dag-aux
  (defthm compose-term-and-dag-aux-return-type
    (implies (and (pseudo-dagp dag)
                  (pseudo-termp term)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))
                  )
             (and (pseudo-dagp (mv-nth 1 (compose-term-and-dag-aux term var-replacement-alist dag)))
                  ;;(dargp (mv-nth 0 (compose-term-and-dag-aux term var-replacement-alist dag)))
                  (DARGP-LESS-THAN (mv-nth 0 (compose-term-and-dag-aux term var-replacement-alist dag))
                                              (BINARY-+ '1 (TOP-NODENUM (mv-nth 1 (compose-term-and-dag-aux term var-replacement-alist dag)))))
                  (<= (top-nodenum dag)
                      (top-nodenum (mv-nth 1 (compose-term-and-dag-aux term var-replacement-alist dag))))))
    :flag compose-term-and-dag-aux)
  (defthm compose-term-and-dag-aux-lst-return-type
    (implies (and (pseudo-dagp dag)
                  (pseudo-term-listp terms)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))
                  )
             (and (pseudo-dagp (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
                  ;;(all-dargp (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
                  (ALL-DARGP-LESS-THAN (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag))
                                                  (BINARY-+ '1 (TOP-NODENUM (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))))
                  (<= (top-nodenum dag)
                      (top-nodenum (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag))))))
    :flag compose-term-and-dag-aux-lst)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (PSEUDO-TERMP
                            ;;PSEUDO-DAGP
                            DARGP-LESS-THAN
                            dag-exprp0
                            )
                           (DARGP
                            TOP-NODENUM
                            MYQUOTEP
                            ;DARGP-LESS-THAN
                            )))))

(defthm pseudo-dagp-aux-of-mv-nth-1-of-compose-term-and-dag-aux-lst
  (implies (and (pseudo-dagp dag)
                (pseudo-term-listp terms)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))
                )
           (pseudo-dagp-aux (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag))
                            (top-nodenum(mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))))
  :hints (("Goal" :use (:instance compose-term-and-dag-aux-lst-return-type)
           :in-theory (e/d (PSEUDO-DAGP)
                           (compose-term-and-dag-aux-lst-return-type)))))

;might loop
;; (thm
;;  (implies (pseudo-dagp dag)
;;           (integerp (top-nodenum dag))))

(verify-guards compose-term-and-dag-aux
  :hints (("Goal" :expand (pseudo-termp term)
           :use ((:instance compose-term-and-dag-aux-return-type (term (car terms)))
                 (:instance compose-term-and-dag-aux-lst-return-type (terms (cdr term))))
           :in-theory (e/d (pseudo-termp pseudo-dagp-rewrite
                                         dag-exprp0)
                           (compose-term-and-dag-aux-lst-return-type
                            compose-term-and-dag-aux-return-type
                            true-listp symbol-listp
                            weak-dagp-aux

                            compose-term-and-dag-aux
                            dargp
                            top-nodenum
                            myquotep
                            dargp-less-than)))))

;;(compose-term-and-dag-aux '(foo s) (acons 's 1 nil) '((1 bar 0) (0 . v)))

;; TODO: Add a (non-array version of) the function to convert a term to a DAG: repeatedly call add-to-dag (maybe also beta-reduce lambdas).

; allows a subset
(defun check-dag-vars (allowed-vars dag)
  (let ((actual-vars (dag-vars dag)))
    (if (subsetp-eq actual-vars allowed-vars)
        dag
      (hard-error 'check-dag-vars "unexpected vars (got: ~x0, expected ~x1) in dag: ~X23"
                  (acons #\0 actual-vars
                         (acons #\1 allowed-vars
                                (acons #\2 dag
                                       (acons #\3 nil nil))))))))

;; Recognize a DAG or a quoted constant (often the result of rewriting a DAG)
(defun weak-dag-or-quotep (obj)
  (declare (xargs :guard t))
  (or (weak-dagp obj)
      (myquotep obj)))

(defun print-dag-or-quotep (obj)
  (declare (xargs :guard (weak-dag-or-quotep obj)))
  (if (quotep obj)
      (cw "~x0~%" obj)
    (print-list obj)))

;deprecate? maybe not. first add the functionality to get-subdag?
(defund drop-nodes-past (nodenum dag-lst)
  (declare (xargs :guard (and (natp nodenum)
                              (weak-dagp-aux dag-lst))))

  (if (endp dag-lst)
      nil
    (let* ((entry (car dag-lst))
           (nodenum2 (car entry)))
      (if (< nodenum nodenum2)
          (drop-nodes-past nodenum (cdr dag-lst))
        dag-lst))))

(defthm acl2-numberp-of-lookup-equal
  (implies (and (nat-listp (strip-cdrs alist))
                (lookup-equal key alist))
           (acl2-numberp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm natp-of-lookup-equal
  (implies (and (nat-listp (strip-cdrs alist))
                (lookup-equal key alist))
           (natp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthmd natp-of-+-of-1
  (implies (natp x)
           (natp (+ 1 x))))

;(local (in-theory (disable 3-CDRS)))

;does not include inlined constants
(defun dag-constants-aux (dag acc)
  (declare (xargs :guard (and (alistp dag)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable alistp)))))
  (if (endp dag)
      acc
    (let* ((entry (first dag))
           (expr (cdr entry)))
      (dag-constants-aux (cdr dag)
                         (if (quotep expr)
                             (add-to-set-equal expr acc)
                           acc)))))

(defun dag-constants (dag)
  (declare (xargs :guard (alistp dag)))
  (dag-constants-aux dag nil))

(defthm symbolp-of-car-of-lookup-equal
  (implies (and (weak-dagp-aux dag)
;                (<= nodenum-or-quotep (car (car dag)))
                ;(natp nodenum-or-quotep)
                )
           (symbolp (car (lookup-equal nodenum-or-quotep dag)))))

(defthm symbolp-of-car-of-lookup-equal-when-weak-dagp
  (implies (and (weak-dagp dag)
;                (<= nodenum-or-quotep (car (car dag)))
                ;(natp nodenum-or-quotep)
                )
           (symbolp (car (lookup-equal nodenum-or-quotep dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

;; ;; good-dag-at-nodenump is what we need to justify processing a dag by
;; ;; repeatedly looking up child nodes.  Does check that children are less than
;; ;; their parents. not enforce that there are no gaps in the numbering.

;; (mutual-recursion
;;  (defun good-dag-at-nodenump (dag nodenum-or-quotep)
;;    (declare (xargs :guard (and (or (myquotep nodenum-or-quotep)
;;                                    (natp nodenum-or-quotep))
;;                                (alistp dag) ;not needed if it's a quotep
;;                                )
;;                    :measure (dag-walker-measure-for-item nodenum-or-quotep)))
;;    (if (not (natp nodenum-or-quotep)) ;must be a constant
;;        t
;;      (let* ((nodenum nodenum-or-quotep)
;;             (res (assoc nodenum dag)))
;;        (and res ;node must be present in the dag
;;             (let ((expr (cdr res)))
;;               (and (bounded-dag-exprp nodenum expr)
;;                    (if (and (consp expr)
;;                             (not (eq 'quote (car expr))))
;;                        (good-dag-at-nodenumsp dag (dargs expr))
;;                      t)))))))

;;  (defun good-dag-at-nodenumsp (dag nodenums-and-quoteps)
;;    (declare (xargs :guard (and (all-dargp nodenums-and-quoteps)
;;                                (true-listp nodenums-and-quoteps)
;;                                (alistp dag) ;not needed if they are all quoteps
;;                                )
;;                    :measure (dag-walker-measure-for-items nodenums-and-quoteps)))
;;    (if (endp nodenums-and-quoteps)
;;        t
;;      (and (good-dag-at-nodenump dag (first nodenums-and-quoteps))
;;           (good-dag-at-nodenumsp dag (rest nodenums-and-quoteps))))))

;; (defthm symbolp-of-lookup-equal
;;   (implies (and (syntaxp (want-to-weaken (symbolp (lookup-equal nodenum-or-quotep dag))))
;;                 (good-dag-at-nodenump dag nodenum-or-quotep)
;;                 (natp nodenum-or-quotep)
;;                 )
;;            (equal (symbolp (lookup-equal nodenum-or-quotep dag))
;;                   (not (consp (lookup-equal nodenum-or-quotep dag)))))
;;   :hints (("Goal" :in-theory (enable LOOKUP-EQUAL))))

;; (defthm symbolp-of-car-of-lookup-equal-when-good-dag-at-nodenump
;;   (implies (and (natp nodenum-or-quotep)
;;                 (good-dag-at-nodenump dag nodenum-or-quotep))
;;            (symbolp (car (lookup-equal nodenum-or-quotep dag))))
;;   :hints (("Goal" :expand ((good-dag-at-nodenump dag nodenum-or-quotep))
;;            :in-theory (enable lookup-equal))))

;; ;; todo: use a custom function instead of lookup to lookup a node in a dag?
;; (defthm true-listp-of-dargs-of-lookup-equal-when-good-dag-at-nodenump
;;   (implies (and (natp nodenum-or-quotep)
;;                 (good-dag-at-nodenump dag nodenum-or-quotep))
;;            (true-listp (dargs (lookup-equal nodenum-or-quotep dag))))
;;   :hints (("Goal" :expand ((good-dag-at-nodenump dag nodenum-or-quotep))
;;            :in-theory (enable lookup-equal
;;                               dargs ;this theorem happens to work for quoteps
;;                               ))))

;; (defthm all-dargp-of-dargs-of-lookup-equal-when-good-dag-at-nodenump
;;   (implies (and (natp nodenum-or-quotep)
;;                 (good-dag-at-nodenump dag nodenum-or-quotep)
;;                 (not (eq 'quote (car (lookup-equal nodenum-or-quotep dag))))
;;                 )
;;            (all-dargp (dargs (lookup-equal nodenum-or-quotep dag))))
;;   :hints (("Goal" :expand ((good-dag-at-nodenump dag nodenum-or-quotep))
;;            :in-theory (enable lookup-equal))))

;; (defthm good-dag-at-nodenumsp-of-dargs-of-lookup-equal-when-good-dag-at-nodenump
;;   (implies (and (natp nodenum-or-quotep)
;;                 (good-dag-at-nodenump dag nodenum-or-quotep)
;;                 (not (eq 'quote (car (lookup-equal nodenum-or-quotep dag))))
;;                 )
;;            (good-dag-at-nodenumsp dag (dargs (lookup-equal nodenum-or-quotep dag))))
;;   :hints (("Goal" :expand ((good-dag-at-nodenump dag nodenum-or-quotep))
;;            :in-theory (enable lookup-equal))))

;; (defun good-dagp (dag)
;;   (declare (xargs :guard t))
;;   (and (alistp dag) ;drop?
;;        (consp dag)
;;        (let ((top-nodenum (top-nodenum dag)))
;;          (and (natp top-nodenum)
;;               (good-dag-at-nodenump dag top-nodenum)))))

;; test: (dag-equal-term-at-node '((2 foo 1 0) (1 quote 3) (0 . x)) '(foo '3 x) 2)
;; test: (not (dag-equal-term-at-node '((2 foo 1 0) (1 quote 3) (0 . x)) '(foo '3 y) 2))

;; similar to (append (keep-atoms items) acc).
(defund append-atoms (items acc)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      acc
    (let ((item (first items)))
      (append-atoms (rest items)
                    (if (atom item)
                        (cons item acc)
                      acc)))))

(defthm all-<-of-append-atoms
  (equal (all-< (append-atoms args acc) bound)
         (and (all-< (keep-atoms args) bound)
              (all-< acc bound)))
  :hints (("Goal" :in-theory (enable keep-atoms append-atoms all-<))))

(defthm true-listp-of-append-atoms
  (implies (true-listp acc)
           (true-listp (append-atoms args acc)))
  :hints (("Goal" :in-theory (enable append-atoms))))

(defthm nat-listp-of-append-atoms
  (implies (and (all-dargp args)
                (nat-listp acc))
           (nat-listp (append-atoms args acc)))
  :hints (("Goal" :in-theory (enable append-atoms nat-listp))))




;kill
;i guess this is a weakend obligation for checking that an arg is a quoted thing?
;; (defthm <-of-len-of-nth-of-dargs-and-3
;;   (implies (and (dag-exprp0 expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (car expr)))
;; ;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 )
;;            (< (len (nth n (dargs expr))) 3))
;;   :hints (("Goal" :in-theory (enable <-of-len-of-nth-and-3-when-all-dargp))))

;kill
;; (defthm not-<-of-len-of-nth-of-dargs-and-2
;;   (implies (and (dag-exprp0 expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (car expr)))
;; ;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 )
;;            (not (< 2 (len (nth n (dargs expr))))))
;;   :hints (("Goal" :use (:instance <-of-len-of-nth-of-dargs-and-3)
;;            :in-theory (disable <-of-len-of-nth-of-dargs-and-3))))

;kill
;; (defthm <-of-1-and-len-of-nth-of-dargs
;;   (implies (and (dag-exprp0 expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (car expr)))
;; ;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 )
;;            (equal (< 1 (len (nth n (dargs expr))))
;;                   (consp (nth n (dargs expr)))))
;;   :hints (("Goal" :in-theory (enable <-of-1-and-len-of-nth-when-all-dargp))))

(defthm car-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (natp top-nodenum))
           (equal (car (car dag-lst))
                  top-nodenum))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm bounded-natp-alistp-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (< top-nodenum bound)
                (natp top-nodenum)
                (natp bound))
           (bounded-natp-alistp dag-lst bound))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-natp-alistp))))

(defthm len-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (natp top-nodenum))
           (equal (len dag-lst)
                  (+ 1 (car (car dag-lst)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd len-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (consp dag))
           (equal (len dag)
                  (+ 1 (car (car dag)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm max-key-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (acl2-numberp max-so-far) ;may not be needed
                (natp top-nodenum))
           (equal (max-key dag-lst max-so-far)
                  (max (car (car dag-lst))
                       max-so-far)))
  :hints (("Goal" ;:cases ()
           :do-not '(generalize)
           :in-theory (enable pseudo-dagp-aux max-key))))

(defthm max-key-when-pseudo-dagp
  (implies (and (pseudo-dagp dag-lst)
                (acl2-numberp max-so-far) ;may not be needed
                )
           (equal (max-key dag-lst max-so-far)
                  (max (car (car dag-lst))
                       max-so-far)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm nth-0-of-nth-0-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag-lst)
           (equal (nth 0 (nth 0 dag-lst))
                  (+ -1 (len dag-lst))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm assoc-equal-when-PSEUDO-DAGP-AUX
 (IMPLIES (AND (PSEUDO-DAGP-AUX DAG-LST m)
               (<= N m)
               (natp N)
               (natp m))
          (ASSOC-EQUAL N DAG-LST))
 :hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX))))

(defthmd assoc-equal-when-PSEUDO-DAGP
  (IMPLIES (AND (PSEUDO-DAGP DAG-LST)
                (<= N (CAR (CAR DAG-LST)))
                (natp N))
           (ASSOC-EQUAL N DAG-LST))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP))))

(defthm dag-exprp0-of-lookup-equal-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (<= n (top-nodenum dag))
                (natp n))
           (dag-exprp0 (lookup-equal n dag)))
  :hints (("Goal" :use (:instance dag-exprp-of-lookup-equal-when-pseudo-dagp)
           :in-theory (disable dag-exprp-of-lookup-equal-when-pseudo-dagp))))

(defthm not-<-of-plus1-of-largest-non-quotep-when-all-dargp-less-than
  (implies (and (all-dargp-less-than nodenum-or-quotep-or-lst bound)
                (natp bound))
           (not (< bound (+ 1 (largest-non-quotep nodenum-or-quotep-or-lst)))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthmd largest-non-quotep-when-all-myquotep
  (implies (all-myquotep items)
           (equal (largest-non-quotep items)
                  -1))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

;disable?
(defthm all-integerp-of-strip-cars-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (all-integerp (strip-cars dag))))

;todo: why didn't dag-walker-measure-for-item work here?  may need some mbts
(mutual-recursion
 (defun dag-equal-term-at-node (dag term nodenum-or-quotep)
   (declare (xargs :guard (and (or (myquotep nodenum-or-quotep)
                                   (natp nodenum-or-quotep))
                               (pseudo-dagp dag) ;(alistp dag)
                               (if (not (consp nodenum-or-quotep)) ;check for nodenum
                                   (<= nodenum-or-quotep (top-nodenum dag))
                                 t)
                               (pseudo-termp term))
                   :guard-hints (("Goal" :expand ((PSEUDO-DAGP-AUX DAG NODENUM-OR-QUOTEP))
                                  :use (:instance dag-exprp-of-lookup-equal-when-pseudo-dagp (n NODENUM-OR-QUOTEP))
                                  :in-theory (e/d (all-dargp-less-than dag-exprp0)
                                                  (len true-listp dag-exprp-of-lookup-equal-when-pseudo-dagp))
                                  :do-not '(generalize eliminate-destructors)
                                  ))
                   :measure (acl2-count term)))
   (if (quotep nodenum-or-quotep)
       (equal nodenum-or-quotep term)
     (let ((expr (lookup nodenum-or-quotep dag)))
       (if (symbolp expr)
           (equal expr term)
         (if (quotep expr)
             (equal expr term)
           ;; it's a function call
           (and (consp term)
                (eq (ffn-symb expr) (ffn-symb term))
                (if (eql (len (dargs expr)) (len (fargs term))) ;should always be true
                    t
                  (er hard? 'dag-equal-term-at-node "Arity mismatch: ~x0, ~x1." expr term))
                (dag-equal-terms-at-nodes dag (fargs term) (dargs expr))))))))

 (defun dag-equal-terms-at-nodes (dag terms nodenums-and-quoteps)
   (declare (xargs :guard (and (pseudo-dagp dag)
                               (all-dargp-less-than nodenums-and-quoteps (+ 1 (top-nodenum dag)))
                               (true-listp nodenums-and-quoteps)
                               (pseudo-term-listp terms)
                               (equal (len terms) (len nodenums-and-quoteps)))
                   :measure (acl2-count terms)))
   (if (endp terms)
       t
     (and (dag-equal-term-at-node dag (first terms) (first nodenums-and-quoteps))
          (dag-equal-terms-at-nodes dag (rest terms) (rest nodenums-and-quoteps))))))

;; (defun dag-equal-term (dag term)
;;   (declare (xargs :guard (and (good-dagp dag)
;;                               (pseudo-termp term))))
;;   (dag-equal-term-at-node dag term (top-nodenum dag)))

;enable?
(defthmd top-nodenum-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (top-nodenum dag)
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable top-nodenum pseudo-dagp))))

(defthm natp-of-top-nodenum-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (natp (top-nodenum dag)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

;mixes car and "nth 0"
(defthm car-of-nth-0-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (car (nth 0 dag))
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

(defthm dargp-less-than-of-nth-when-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (natp n)
                (< n (len vals)))
           (dargp-less-than (nth n vals) bound))
  :hints
  (("Goal" :in-theory (enable all-dargp-less-than))))

(defthm dargp-less-than-when-myquotep-cheap
  (implies (myquotep item)
           (dargp-less-than item bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm dargp-less-than-when-equal-of-nth-0-and-quote
  (implies (and (equal 'quote (nth 0 item))
                (dargp item))
           (dargp-less-than item bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm pseudo-dagp-aux-forward-to-true-listp
  (implies (pseudo-dagp-aux dag-lst current-nodenum)
           (true-listp dag-lst))
  :rule-classes :forward-chaining)

(defthm pseudo-dagp-aux-of-cons-of-cons
  (implies (integerp nodenum)
           (equal (pseudo-dagp-aux (cons (cons nodenum expr) dag) nodenum)
                  (and (natp nodenum)
                       (bounded-dag-exprp nodenum expr)
                       (pseudo-dagp-aux dag (+ -1 nodenum)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-nil
  (equal (pseudo-dagp-aux nil current-nodenum)
         (< current-nodenum 0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-car-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag num)
                (natp num)
                )
           (pseudo-dagp-aux dag (car (car dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;; can introduce all-dargp-less-than out of nowhere, so kept disabled
(defthmd not-<-of-nth-when-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (natp n)
                (< n (len vals))
                ;; (not (consp val))
                (natp bound))
           (not (< bound (nth n vals))))
  :hints (("Goal" :in-theory (enable all-dargp-less-than nth))))

(defthm not-<-of-nth-when-all-dargp-less-than-gen-constant
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (all-dargp-less-than vals bound)
                ;; (natp n)
                ;; (< n (len vals))
                ;; (not (consp val))
                )
           (not (< (nth n vals) k)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than dargp-less-than nth))))

;; move these?

(defun quoted-natp (item)
  (declare (xargs :guard (dargp item)))
  (and (consp item)
       (natp (unquote item))))

(defun quoted-posp (item)
  (declare (xargs :guard (dargp item)))
  (and (consp item)
       (posp (unquote item))))

(defthm not-<-of-+-1-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than items dag-len)
                (natp n)
                (< n (len items))
                (natp dag-len)
                (not (consp (nth n items))))
           (not (< dag-len (+ 1 (nth n items)))))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than nth)
                                  ()))))

(defthm all-dargp-less-than-when-all-<
  (implies (and (all-< items bound)
                (all-natp items))
           (all-dargp-less-than items bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than all-< all-natp))))

(defthm all-dargp-less-than-of-dargs-when-<-simple
  (implies (and (bounded-dag-exprp limit expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                )
           (all-dargp-less-than (dargs expr) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;drop?
(defthmd all-dargp-less-than-of-dargs-when-<
  (implies (and (< nodenum limit)
                (bounded-dag-exprp nodenum expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                )
           (all-dargp-less-than (dargs expr) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;; use consp as our normal form
(defthm len-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than items bound)
                (< (nfix n) (len items)))
           (equal (len (nth n items))
                  (if (consp (nth n items))
                      2
                    0)))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than nth) ()))))

(defthm len-of-nth-when-all-dargp
  (implies (and (all-dargp items)
                (< (nfix n) (len items)))
           (equal (len (nth n items))
                  (if (consp (nth n items))
                      2
                    0)))
  :hints (("Goal" :in-theory (e/d (all-dargp nth) ()))))

;; (defthm <-of-car-when-all-dargp-less-than
;;   (implies (and (all-dargp-less-than items bound)
;;                 (not (consp (car items)))
;;                 (consp items))
;;            (< (car items) bound))
;;   :hints (("Goal" :in-theory (e/d (all-dargp-less-than) ()))))

(defthm bounded-natp-alistp-when-pseudo-dagp
  (implies (pseudo-dagp dag-lst)
           (bounded-natp-alistp dag-lst (len dag-lst)))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux bounded-natp-alistp))))

(defthm bounded-natp-alistp-when-pseudo-dagp-gen
  (implies (and (pseudo-dagp dag)
                (<= (len dag) bound)
                (natp bound))
           (bounded-natp-alistp dag bound))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthmd car-of-car-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag-lst)
           (equal (car (car dag-lst))
                  (+ -1 (len dag-lst))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm acl2-numberp-of-largest-non-quotep
  (implies (all-dargp items)
           (acl2-numberp (largest-non-quotep items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable ALL-DARGP LARGEST-NON-QUOTEP))))

(defthm myquotep-of-cdr-of-assoc-equal
  (implies (and (assoc-equal form alist)
                (equal 'quote (cadr (assoc-equal form alist)))
                (all-dargp (strip-cdrs alist)))
           (myquotep (cdr (assoc-equal form alist))))
  :hints (("Goal" :use (:instance dargp-of-cdr-of-assoc-equal (var form))
           :in-theory (disable dargp-of-cdr-of-assoc-equal
                               dargp-when-equal-of-quote-and-car-cheap))))

(defthm <=-of-largest-non-quotep-when-all-dargp-less-than
  (implies (and (all-dargp-less-than items (+ 1 bound))
                (natp bound))
           (<= (largest-non-quotep items) bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than
                                     largest-non-quotep))))

(defthm <-of-largest-non-quotep-of-dargs-when-dag-exprp
  (implies (and (bounded-dag-exprp (+ 1 n) expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                (natp n))
           (not (< n (largest-non-quotep (dargs expr)))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm <-of-LARGEST-NON-QUOTEP-of-dargs
  (implies (and (bounded-dag-exprp nodenum expr)
                (not (equal 'quote (car expr)))
                (natp nodenum))
           (< (LARGEST-NON-QUOTEP (DARGS expr))
              nodenum))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;remove the other?
(defthm <-of-largest-non-quotep-of-dargs-when-dag-exprp-gen
  (implies (and (bounded-dag-exprp (+ 1 n) expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                (integerp n) ;this version
                (<= -1 N) ;this version
                )
           (not (< n (largest-non-quotep (dargs expr)))))
  :hints (("Goal" :cases ((< n 0))
           :in-theory (enable bounded-dag-exprp all-dargp-less-than-when-non-positive))))

;todo: limit?
;move
(defthm consp-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (natp top-nodenum)
                )
           (consp (car dag-lst)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm consp-of-car-when-pseudo-dagp-aux-2
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (consp dag-lst))
           (consp (car dag-lst)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm natp-of-car-of-car-when-pseudo-dagp-aux-2
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (natp top-nodenum))
           (natp (car (car dag-lst))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm consp-of-car-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (consp (car dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm dag-exprp0-of-cdr-of-car-when-weak-dagp
  (implies (weak-dagp dag)
           (dag-exprp0 (cdr (car dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm pseudo-dagp-forward-to-consp-of-car
  (implies (pseudo-dagp dag)
           (consp (car dag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm pseudo-dagp-forward-to-consp-of-nth-0
  (implies (pseudo-dagp dag)
           (consp (nth 0 dag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm pseudo-dagp-forward-to-consp
  (implies (pseudo-dagp dag)
           (consp dag))
  :rule-classes :forward-chaining)

(defthm all-<-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (all-< (strip-cars dag) (len dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

(defthm all-<-of-strip-cars-of-+-1-of-top-nodenum
  (implies (pseudo-dagp dag)
           (all-< (strip-cars dag) (+ 1 (top-nodenum dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))


;disable or limit?
(defthm weak-dagp-aux-when-pseudo-dagp
  (implies (pseudo-dagp x)
           (weak-dagp-aux x))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP))))

(defthmd car-of-nth-of-+-of--1-and-len-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (natp current-nodenum))
           (equal (car (nth (+ -1 (len dag)) dag))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd car-of-nth-of-+-of-car-of-car--when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (natp current-nodenum))
           (equal (car (nth (car (car dag)) dag))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd car-of-nth-of-+-of--1-and-len-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (car (nth (+ -1 (len dag)) dag))
                  0))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp
                                   car-of-nth-of-+-of-car-of-car--when-pseudo-dagp-aux)
                                  (;nth-of-cdr
                                   )))))

(defthm car-of-nth-of-+-of--1-and-len-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag)
           (equal (car (NTH (+ -1 (LEN dag)) dag))
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable car-of-nth-of-+-of--1-and-len-when-pseudo-dagp))))

(defthmd nth-0-of-nth-of-+-of--1-and-len-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (nth 0 (nth (+ -1 (len dag)) dag))
                  0))
  :hints (("Goal" :use (:instance car-of-nth-of-+-of--1-and-len-when-pseudo-dagp)
           :in-theory (e/d (nth)
                           (;nth-of-cdr
                            car-of-nth-of-+-of--1-and-len-when-pseudo-dagp
                            car-of-nth-of-+-of--1-and-len-when-pseudo-dagp-cheap)))))

(defthm nth-0-of-nth-of-+-of--1-and-len-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag)
           (equal (nth 0 (nth (binary-+ '-1 (len dag)) dag))
                  0))
  :hints (("Goal" :use (:instance nth-0-of-nth-of-+-of--1-and-len-when-pseudo-dagp)
           :in-theory (e/d (nth) (;nth-of-cdr
                                  car-of-nth-of-+-of--1-and-len-when-pseudo-dagp)))))

(defthm pseudo-dagp-aux-of-minus1-of-len
  (implies (pseudo-dagp dag)
           (pseudo-dagp-aux dag (binary-+ '-1 (len dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm rational-listp-of-strip-cars-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (integerp current-nodenum))
           (rational-listp (strip-cars dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-dag-exprp strip-cars))))

;here we are getting the nodenum of the last element
(defthm car-of-nth-of-caar-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (natp nodenum))
           (equal (car (nth (car (car dag)) dag))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm all-<-of-strip-cars-and-+-1-of-caar
  (implies (pseudo-dagp-aux dag (car (car dag)))
           (all-< (strip-cars dag)
                  (+ 1 (car (car dag)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux strip-cars))))

(defthm rational-listp-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (rational-listp (strip-cars dag))))

(defthm maxelem-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (maxelem (strip-cars dag))
                  (car (car dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux strip-cars))))


;; ;drop?
;; (defthm pseudo-dagp-aux-of-cdr-lemma
;;   (implies (and (pseudo-dagp-aux dag-lst (car (car dag-lst)))
;;                 (equal (car (car dag-lst)) (+ -1 (len dag-lst)))
;;                 (< 1 (len dag-lst))
;;                 (true-listp dag-lst))
;;            (pseudo-dagp-aux (cdr dag-lst) (car (cadr dag-lst))))
;;   :hints (("Goal" :expand ((pseudo-dagp-aux dag-lst (car (car dag-lst)))
;;                            (PSEUDO-DAGP-AUX (CDR DAG-LST)
;;                                             (CAR (CADR DAG-LST)))
;;                            (PSEUDO-DAGP-AUX (CDR DAG-LST)
;;                                             (+ -1 (CAR (CAR DAG-LST))))))))

;; (defthmd integerp-of-car-of-car-when-pseudo-dagp-aux
;;   (implies (and (pseudo-dagp-aux dag nodenum)
;;                 (consp dag)
;;                 (integerp nodenum))
;;            (integerp (car (car dag))))
;;   :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;; (local (in-theory (enable integerp-of-car-of-car-when-pseudo-dagp-aux)))

;; ;todo: some of this stuff is not needed

;; (defthm PSEUDO-DAGP-AUX-of-cdr-lemma2
;;   (implies (and (PSEUDO-DAGP-AUX REV-DAG-LST (+ -1 (LEN REV-DAG-LST)))
;;                 (consp REV-DAG-LST))
;;            (PSEUDO-DAGP-AUX (CDR REV-DAG-LST) (+ -2 (LEN REV-DAG-LST))))
;;   :hints (("Goal" :expand (PSEUDO-DAGP-AUX REV-DAG-LST (+ -1 (LEN REV-DAG-LST)))
;;            :in-theory (disable LEN-WHEN-PSEUDO-DAGP-AUX))))

;; (local (in-theory (disable LEN-WHEN-PSEUDO-DAGP-AUX))) ;looped!

;; (defthmd caar-of-cdr-when-pseudo-dagp-aux
;;   (implies (and (pseudo-dagp-aux dag (+ -1 (len dag)))
;;                 (consp (cdr dag)))
;;            (equal (car (car (cdr dag)))
;;                   (+ -2 (len dag))))
;;   :hints (("Goal" :expand ((pseudo-dagp-aux dag (+ -1 (len dag)))
;;                            (PSEUDO-DAGP-AUX (CDR DAG)
;;                                             (+ -1 (CAR (CAR DAG))))))))


;move?
(defthm <-of-largest-non-quotep-of-dargs-2
  (implies (and (bounded-dag-exprp nodenum expr)
                (natp nodenum)
                (consp expr)
                (not (equal (car expr) 'quote)))
           (not (< (+  -1 nodenum)
                   (largest-non-quotep (dargs expr)))))
  :hints (("Goal" :use (:instance <-of-largest-non-quotep-of-dargs-when-dag-exprp
                                  (n (+ -1 nodenum)))
           :expand (bounded-dag-exprp 0 expr)
           :in-theory (disable <-of-largest-non-quotep-of-dargs-when-dag-exprp))))

(defthm dargp-of-lookup-equal-when-all-dargp-less-than-of-strip-cdrs
  (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                (lookup-equal var alist))
           (dargp (lookup-equal var alist)))
  :hints (("Goal" :induct t
           :in-theory (e/d (all-dargp-less-than lookup-equal strip-cdrs
                                                           dargp-less-than)
                           (myquotep)))))

(defthmd <-of-lookup-equal-when-all-dargp-less-than-of-strip-cdrs
  (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                (lookup-equal var alist)
                (not (consp (lookup-equal var alist))))
           (< (lookup-equal var alist) dag-len))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than lookup-equal strip-cdrs)
                                  (myquotep)))))


;;;
;;; top-nodenum-of-dag
;;;

;this one has a better guard
;deprecate the other one?
(defund top-nodenum-of-dag (dag)
  (declare (xargs :GUARD (pseudo-dagp dag)
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))
                  ))
  (let* ((entry (car dag))
         (nodenum (car entry)))
    nodenum))

(defthmd top-nodenum-of-dag-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (top-nodenum-of-dag dag)
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable top-nodenum-of-dag pseudo-dagp))))

;temporary
(defthmd top-nodenum-of-dag-becomes-top-nodenum
  (implies (pseudo-dagp dag)
           (equal (top-nodenum-of-dag dag)
                  (top-nodenum dag)))
  :hints (("Goal" :in-theory (enable top-nodenum top-nodenum-of-dag))))

(defthm natp-of-top-nodenum-of-dag
  (implies (pseudo-dagp dag)
           (natp (top-nodenum-of-dag dag)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable top-nodenum-of-dag))))
