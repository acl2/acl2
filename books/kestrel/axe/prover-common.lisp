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
(include-book "kestrel/utilities/conjuncts-and-disjuncts" :dir :system) ; for negate-terms
(include-book "kestrel/bv/bvif" :dir :system) ; since the prover knows about BVIF
(include-book "kestrel/bv/bool-to-bit" :dir :system) ; since the prover knows about BOOL-TO-BIT
(include-book "all-less-than-or-equal")
(include-book "merge-sort-less-than")
(include-book "supporting-nodes")
(include-book "dag-array-builders")
(include-book "renaming-array")
(include-book "translation-array")
(include-book "unify-tree-and-dag")
(include-book "merge-term-into-dag-array-basic")
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "def-dag-builder-theorems")
(include-book "crunch-dag2")
(include-book "worklists")
(include-book "equivs")
(include-book "rebuild-nodes")
(include-book "dag-array-printing")
;(include-book "splitting")
;(include-book "elim")
(include-book "kestrel/booleans/boolor" :dir :system) ;since this book knows about boolor
(include-book "kestrel/booleans/booland" :dir :system) ;since this book knows about booland
(include-book "dag-size2")
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
;trim?:
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/add-to-set-equal" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
;(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "check-equivs"))

(local (in-theory (disable add-to-set-equal)))



(local
 (defthm rationalp-when-integerp
   (implies (integerp x)
            (rationalp x))))



;dup
(defthmd consp-when-<-of-0-and-nth
  (implies (< 0 (NTH n x))
           (consp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defund keep-non-atoms (items)
  (declare (xargs :guard t))
  (if (atom items) ;would endp be faster here?
      nil
    (if (atom (car items))
        (keep-non-atoms (cdr items))
      (cons (car items) (keep-non-atoms (cdr items))))))

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

;move?
(defund make-var-lookup-terms (vars alist-nodenum)
  (declare (xargs :guard (true-listp vars)))
  (if (endp vars)
      nil
    (cons `(lookup-equal ',(car vars) ,alist-nodenum)
          (make-var-lookup-terms (cdr vars) alist-nodenum))))

;; An entry in the equiv-table means, for example, "If we are trying to
;; preserve iff, and we are rewriting a boolor, use iff and iff for the args."

;; Currently only 'equal and 'iff are supported as equivs.
;; No entries are needed here for IF, MYIF, or BOOLIF, because all Axe provers handle them specially.
;; We could drop BVIF except the simple provers do not (yet) handle it specially.
(defconst *equiv-alist*
  (acons 'iff ; outer equiv that must be preserved
         (acons 'not '(iff)
                (acons 'iff '(iff iff)
                       (acons 'implies '(iff iff)
                              (acons 'bool-to-bit '(iff)
                                     (acons 'bool-fix$inline '(iff)
                                            ;; TODO: Remove this?  A BVIF in an IFF context is just T:
                                            ;; (acons 'bvif '(equal iff equal equal)
                                            (acons 'boolor '(iff iff)
                                                   (acons 'boolxor '(iff iff)
                                                          (acons 'booland '(iff iff)
                                                                 nil)))
                                            ;;)
                                            )))))
         (acons 'equal ; outer equiv that must be preserved
                ;; We only include things here for which we can do better than using
                ;; an equiv of EQUAL for all arguments:
                (acons 'not '(iff)
                       (acons 'iff '(iff iff)
                              (acons 'implies '(iff iff)
                                     (acons 'bool-to-bit '(iff)
                                            (acons 'bool-fix$inline '(iff)
                                                   (acons 'bvif '(equal iff equal equal)
                                                          (acons 'boolor '(iff iff)
                                                                 (acons 'boolxor '(iff iff)
                                                                        (acons 'booland '(iff iff)
                                                                               nil)))))))))
                nil)))

(thm
 (equiv-alistp *equiv-alist*))

;; This generates THMs to check that *equiv-alist* is correct.
(local (check-equiv-alist *equiv-alist*))

;; copies a segment of nodes from FROM-DAG-ARRAY to DAG-ARRAY and returns the new dag (including the auxiliary data structures) and a RENAMING-ARRAY
;; Returns (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array).
;fixme should this use a worklist instead of copying a segment?
(defund add-array-nodes-to-dag (nodenum ;smallest nodenum to copy
                                max-nodenum ;largest nodenum to copy
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
                                       dag-parent-array   ;;just passed through
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

(defthm add-array-nodes-to-dag-return-type
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (integerp max-nodenum)
                (natp nodenum)
                (pseudo-dag-arrayp from-dag-array-name from-dag-array from-dag-array-len)
                (< max-nodenum from-dag-array-len)
                (<= nodenum (+ 1 max-nodenum))
                (renaming-arrayp 'renaming-array renaming-array nodenum) ;todo: add more guards?
                (<= (+ 1 max-nodenum)
                    (alen1 'renaming-array renaming-array))
                (bounded-renaming-entriesp (+ -1 nodenum) 'renaming-array renaming-array dag-len))
           (mv-let (erp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-renaming-array)
             (add-array-nodes-to-dag nodenum max-nodenum
                                     from-dag-array-name from-dag-array from-dag-array-len
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                     renaming-array)
             (implies (not erp)
                      (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                           (renaming-arrayp 'renaming-array new-renaming-array nodenum)
                           (equal (alen1 'renaming-array new-renaming-array)
                                  (alen1 'renaming-array renaming-array))
                           ;;follows from the above:
                           (array1p 'renaming-array new-renaming-array)))))
  :hints (("Goal" :induct (ADD-ARRAY-NODES-TO-DAG NODENUM MAX-NODENUM
                                                  FROM-DAG-ARRAY-NAME FROM-DAG-ARRAY
                                                  FROM-DAG-ARRAY-LEN DAG-ARRAY DAG-LEN
                                                  DAG-PARENT-ARRAY DAG-CONSTANT-ALIST
                                                  DAG-VARIABLE-ALIST RENAMING-ARRAY)
           :in-theory (enable add-array-nodes-to-dag
                              RENAMING-ARRAYP ;todo
                              ))))

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

(defthm not-<-of-nth-when-all-natp
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (all-natp x))
           (not (< (nth n x) k)))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

;; Returns (mv success-flg alist-for-free-vars).
;; hyp is a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars
;; if success-flg is nil, the alist returned is irrelevant
;; the alist returned maps variables to nodenums or quoteps
(defund match-hyp-with-nodenum-to-assume-false (hyp nodenum-to-assume-false dag-array dag-len)
  (declare (xargs :guard (and (axe-treep hyp)
                              (consp hyp)
                              (not (equal 'quote (ffn-symb hyp)))
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp nodenum-to-assume-false)
                              (< nodenum-to-assume-false dag-len))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))
           (ignore dag-len) ;todo
           )
  (if (and (call-of 'not hyp) ;; TODO: Avoid checking this over and over.  Also, do we know that hyp is always a cons?
           (consp (fargs hyp)) ; for the guard proof, should always be true if arities are right.
           )
      ;; If hyp is of the form (not <x>) then try to match <x> with the nodenum-to-assume-false:
      ;; TODO: what if hyp is of the form (equal .. nil) or (equal nil ..)?
      (unify-tree-with-dag-node (farg1 hyp) nodenum-to-assume-false dag-array nil)
    ;;otherwise we require the expr assumed false to be a call of NOT
    (let ((expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false))) ;could do this at a shallower level?
      (if (and (call-of 'not expr-to-assume-false)
               (consp (dargs expr-to-assume-false)) ; for the guard proof, should always be true if arities are right.
               )
          (let ((arg (darg1 expr-to-assume-false)))
            (if (consp arg) ;whoa, it's a constant!
                (mv nil nil)
              (unify-tree-with-dag-node hyp arg dag-array nil)))
        (mv nil nil)))))

(defthm symbol-alistp-of-mv-nth-1-of-match-hyp-with-nodenum-to-assume-false
  (symbol-alistp (mv-nth 1 (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
  :hints (("Goal" :in-theory (enable match-hyp-with-nodenum-to-assume-false))))

(defthm true-listp-of-mv-nth-1-of-match-hyp-with-nodenum-to-assume-false
  (true-listp (mv-nth 1 (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable match-hyp-with-nodenum-to-assume-false))))

(defthm all-dargp-of-mv-nth-1-of-match-hyp-with-nodenum-to-assume-false
  (implies (and (axe-treep hyp)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum-to-assume-false)
                (< nodenum-to-assume-false dag-len)
                (mv-nth 0 (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
           (all-dargp (strip-cdrs (mv-nth 1 (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (match-hyp-with-nodenum-to-assume-false car-becomes-nth-of-0 NATP-OF-+-OF-1)
                                  (natp)))))

(defthm all-dargp-less-than-of-mv-nth-1-of-match-hyp-with-nodenum-to-assume-false
  (implies (and (axe-treep hyp)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum-to-assume-false)
                (< nodenum-to-assume-false dag-len)
                (mv-nth 0 (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
           (all-dargp-less-than (strip-cdrs (mv-nth 1 (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))) dag-len))
  :hints (("Goal" :in-theory (e/d (match-hyp-with-nodenum-to-assume-false car-becomes-nth-of-0 NATP-OF-+-OF-1)
                                  (natp)))))

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



;; (defun check-integerp (caller item)
;;   (declare (xargs :guard t))
;;   (if (integerp item)
;;       item
;;     (prog2$ (cw "Error in ~x0: Expected an integer but got ~x1." caller item)
;;             (break$)
;; ;            (hard-error caller nil nil)
;;             )))



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



;;(ALL-<=-ALL (DARGS (AREF1 'DAG-ARRAY DAG-ARRAY nodenum)) WORKLIST)



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

;; A good ordering of substitutions would be to substitute the "smallest" term
;; (the one which will be at the bottom of the DAG after all the substs) into
;; the second smallest, then substitute that into the third smallest, and so
;; on.  Doing so means that only a little bit of structure needs to be rebuilt
;; each time.  A bad ordering would substitute the biggest/highest term (in
;; terms of where it will appear in the resuls) that can be substituted, then
;; put the second biggest into that (on the bottom), etc.  With such an
;; ordering, more and more structure gets rebuilt each time.




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

(defund print-axe-prover-case-aux (literal-nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-natp literal-nodenums)
                              (true-listp literal-nodenums)
                              (all-< literal-nodenums dag-len))))
  (if (endp literal-nodenums)
      nil
    (progn$ (let* ((nodenum (first literal-nodenums))
                   (term-size (nfix (size-of-node nodenum dag-array-name dag-array dag-len)))) ;todo: drop the nfix
              (if (< term-size 10000)
                  (let ((term (dag-to-term-aux-array dag-array-name dag-array nodenum)))
                    (if (and (call-of 'not term)
                             (consp (cdr term)))
                        (cw "~x0~%" (farg1 term))
                      (cw "~x0~%" `(not ,term))))
                (print-negated-literal nodenum dag-array-name dag-array dag-len)))
            (cw "~%")
            (print-axe-prover-case-aux (rest literal-nodenums) dag-array-name dag-array dag-len))))

;recall that the case is the negation of all the literals
;fixme similar name to print-negated-literal-list
(defund print-axe-prover-case (literal-nodenums dag-array-name dag-array dag-len case-adjective)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-natp literal-nodenums)
                              (true-listp literal-nodenums)
                              (all-< literal-nodenums dag-len))))
  (progn$
   (cw "(Negated lits (~x0) for ~s1 case:~%" (len literal-nodenums) case-adjective)
   (print-axe-prover-case-aux literal-nodenums dag-array-name dag-array dag-len)
   (cw ")~%")))

(defthm <-of-+-1-of-maxelem
  (implies (and (all-< lst x)
                (all-integerp lst)
                (integerp x)
                (consp lst))
           (not (< x (+ 1 (MAXELEM lst)))))
  :hints (("Goal" :in-theory (enable maxelem all-<))))

;; ;; Returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
;; ;why is this separate?
;; ;rename?
;; (defund simplify-var-and-add-to-dag-for-axe-prover (var equiv
;;                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                         rule-alist
;;                                                         nodenums-to-assume-false
;;                                                         equiv-alist print
;;                                                         info tries interpreted-function-alist monitored-symbols
;;                                                         ;; embedded-dag-depth
;;                                                         case-designator work-hard-when-instructedp prover-depth)
;;   (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                               (symbolp equiv)
;;                               (symbolp var)
;;                               ;(<= dag-len 2147483645)
;;                               (all-natp nodenums-to-assume-false)
;;                               (true-listp nodenums-to-assume-false)
;;                               (all-< nodenums-to-assume-false dag-len)))
;;            (ignore rule-alist equiv-alist interpreted-function-alist monitored-symbols
;;                    ;;embedded-dag-depth
;;                    case-designator work-hard-when-instructedp
;;                    prover-depth ;fixme
;;                    ))
;;   (prog2$ nil ;;(cw "Rewriting the variable ~x0" var) ;new!
;;           ;; It's a variable:  FFIXME perhaps add it first and then use assumptions?
;;           ;; First try looking it up in the assumptions (fixme make special version of replace-term-using-assumptions-for-axe-prover for a variable?):
;;           ;; TOOD: Could we just rely on variable substitution to handle this?:
;;           (let ((assumption-match (replace-term-using-assumptions-for-axe-prover var equiv nodenums-to-assume-false dag-array print)))
;;             (if assumption-match
;;                 ;; We replace the variable with something it's equated to in nodenums-to-assume-false.
;;                 ;; We don't rewrite the result (by the second pass, nodenums-to-assume-false will be simplified - and maybe we should always do that?)
;; ;fixme what if there is a chain of equalities to follow?
;;                 (mv (erp-nil) assumption-match dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
;;               ;; no match, so we just add the variable to the DAG:
;;               ;;make this a macro? this one might be rare..  same for other adding to dag operations?
;;               (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist) ;fixme simplify nodenum?
;;                 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))

;; ;todo: don't even take tries
;; (defthm mv-nth-8-of-simplify-var-and-add-to-dag-for-axe-prover
;;   (equal (mv-nth 8 (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                rule-alist
;;                                                                nodenums-to-assume-false
;;                                                                equiv-alist print
;;                                                                info tries interpreted-function-alist monitored-symbols
;;                                                                case-designator work-hard-when-instructedp prover-depth))
;;          tries)
;;   :hints (("Goal" :in-theory (enable simplify-var-and-add-to-dag-for-axe-prover))))

;; ;todo: don't even take info
;; (defthm mv-nth-7-of-simplify-var-and-add-to-dag-for-axe-prover
;;   (equal (mv-nth 7 (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                rule-alist
;;                                                                nodenums-to-assume-false
;;                                                                equiv-alist print
;;                                                                info tries interpreted-function-alist monitored-symbols
;;                                                                case-designator work-hard-when-instructedp prover-depth))
;;          info)
;;   :hints (("Goal" :in-theory (enable simplify-var-and-add-to-dag-for-axe-prover))))

;; (defthm <-of-mv-nth-3-of-simplify-var-and-add-to-dag-for-axe-prover
;;   (implies (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;            (<= dag-len
;;                (mv-nth 3 (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                      rule-alist
;;                                                                      nodenums-to-assume-false
;;                                                                      equiv-alist print
;;                                                                      info tries interpreted-function-alist monitored-symbols
;;                                                                      case-designator work-hard-when-instructedp prover-depth))))
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable simplify-var-and-add-to-dag-for-axe-prover))))

;; (defthm simplify-var-and-add-to-dag-for-axe-prover-return-type
;;   (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (symbolp var))
;;            (mv-let (erp nodenum new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
;;              (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                          rule-alist
;;                                                          nodenums-to-assume-false
;;                                                          equiv-alist print
;;                                                          info tries interpreted-function-alist monitored-symbols
;;                                                          case-designator work-hard-when-instructedp prover-depth)
;;              (declare (ignore nodenum info tries))
;;              (implies (not erp)
;;                       (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))))
;;   :hints (("Goal" :in-theory (enable simplify-var-and-add-to-dag-for-axe-prover))))

;; (defthm dargp-less-than-of-mv-nth-1-and-mv-nth-3-of-simplify-var-and-add-to-dag-for-axe-prover
;;   (implies (and (not (mv-nth 0 (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                            rule-alist
;;                                                                            nodenums-to-assume-false
;;                                                                            equiv-alist print
;;                                                                            info tries interpreted-function-alist monitored-symbols
;;                                                                            case-designator work-hard-when-instructedp prover-depth)))
;;                 (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (all-natp nodenums-to-assume-false)
;;                 (all-< nodenums-to-assume-false dag-len))
;;            (dargp-less-than (mv-nth 1 (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                                   rule-alist
;;                                                                                   nodenums-to-assume-false
;;                                                                                   equiv-alist print
;;                                                                                   info tries interpreted-function-alist monitored-symbols
;;                                                                                   case-designator work-hard-when-instructedp prover-depth))
;;                             (mv-nth 3 (simplify-var-and-add-to-dag-for-axe-prover var equiv
;;                                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                                   rule-alist
;;                                                                                   nodenums-to-assume-false
;;                                                                                   equiv-alist print
;;                                                                                   info tries interpreted-function-alist monitored-symbols
;;                                                                                   case-designator work-hard-when-instructedp prover-depth))))
;;   :hints (("Goal" :in-theory (enable simplify-var-and-add-to-dag-for-axe-prover))))

;; This duplicates the term x, but if it's  the variable COUNT, that's ok.
(defmacro zp-fast (x)
  `(mbe :logic (zp ,x)
        :exec (= 0 ,x)))

(defund simple-prover-optionsp (options)
  (declare (xargs :guard t))
  (and (symbol-alistp options)
       (subsetp-eq (strip-cars options) '(:no-splitp ;whether to split into cases
                                          ))))

(defthm simple-prover-optionsp-forward-to-symbol-alistp
  (implies (simple-prover-optionsp options)
           (symbol-alistp options))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable simple-prover-optionsp))))

(defthm all-axe-treep-of-wrap-all
  (equal (all-axe-treep (wrap-all 'not atoms))
         (all-axe-treep atoms))
  :hints (("Goal" :in-theory (enable all-axe-treep wrap-all))))

(defund prover-resultp (result)
  (declare (xargs :guard t))
  (member-equal result '(:proved :failed :timed-out)))
