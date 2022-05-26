; Building DAGs, represented as lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dags")
;todo: reduce?:
(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

;; Note that DAGs are usually built in fast ways that use array, not using the functions in this book

;;;
;;; find-node-for-expr
;;;

;; Looks for the node in DAG whose expression is EXPR.
;returns nil or the nodenum
;like assoc but looks for a given value (second component of an entry), rather than a given key
;; Now only used for vars and constants?
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
                              (dag-exprp expr))
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
                              (dag-exprp expr))
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
  :hints (("Goal" :in-theory (enable add-to-dag))))

(defthm weak-dagp-aux-of-mv-nth-1-of-add-to-dag
  (implies (and (weak-dagp-aux dag)
                (bounded-dag-exprp (+ 1 (top-nodenum dag)) expr))
           (weak-dagp-aux (mv-nth 1 (add-to-dag expr dag))))
  :hints (("Goal" :in-theory (enable add-to-dag acons (:d weak-dagp-aux) BOUNDED-DAG-EXPRP DAG-EXPRP))))

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
  :hints (("Goal" :in-theory (enable add-to-dag pseudo-dagp dargp-less-than))))

(defthm  add-to-dag-of-nil
  (equal (add-to-dag expr nil)
         (mv 0 (acons 0 expr nil)))
  :hints (("Goal" :in-theory (enable add-to-dag))))

(defthm consp-of-mv-nth-1-of-add-to-dag
  (consp (mv-nth 1 (add-to-dag expr dag)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-to-dag find-node-for-expr2))))

;;;
;;; compose-term-and-dag
;;;

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
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag))))
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
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag))))))
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
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))
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
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))
                  )
             (and (pseudo-dagp (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
                  ;;(all-dargp (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))
                  (BOUNDED-DARG-LISTP (mv-nth 0 (compose-term-and-dag-aux-lst terms var-replacement-alist dag))
                                                  (BINARY-+ '1 (TOP-NODENUM (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag)))))
                  (<= (top-nodenum dag)
                      (top-nodenum (mv-nth 1 (compose-term-and-dag-aux-lst terms var-replacement-alist dag))))))
    :flag compose-term-and-dag-aux-lst)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (PSEUDO-TERMP
                            ;;PSEUDO-DAGP
                            DARGP-LESS-THAN
                            dag-exprp)
                           (DARGP
                            TOP-NODENUM
                            ;MYQUOTEP
                            ;DARGP-LESS-THAN
                            )))))

(defthm pseudo-dagp-aux-of-mv-nth-1-of-compose-term-and-dag-aux-lst
  (implies (and (pseudo-dagp dag)
                (pseudo-term-listp terms)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) (+ 1 (top-nodenum dag)))
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
                                         dag-exprp)
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
