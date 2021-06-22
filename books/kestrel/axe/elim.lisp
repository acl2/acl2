; Support for the Axe Prover tuple elimination
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

(include-book "dag-arrays")
(include-book "make-dag-variable-alist")
(include-book "worklists")
(include-book "axe-trees")
(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "dag-array-printing")
(include-book "supporting-vars")
(include-book "rebuild-literals")
(include-book "merge-term-into-dag-array-basic")
(include-book "kestrel/utilities/make-cons-nest" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;dup in prove-with-stp
(defthm assoc-equal-when-member-equal-of-strip-cars
  (implies (and (member-equal key (strip-cars alist))
                (or key (alistp alist)))
           (assoc-equal key alist))
  :hints
  (("Goal" :in-theory (e/d (member-equal assoc-equal strip-cars alistp) nil))))

(defund get-var-length-alist-for-tuple-elimination (nodenums-to-assume-false dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (true-listp nodenums-to-assume-false)
                              (all-natp nodenums-to-assume-false)
                              (all-< nodenums-to-assume-false dag-len))
                  :guard-hints (("Goal" :in-theory (disable pseudo-dag-arrayp)))))
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
(defund nodenum-only-appears-in (worklist dag-array dag-len nodenum fns done-array)
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
                  :guard-hints (("Goal" :in-theory (e/d (;integerp-of-maxelem-when-all-integerp
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
                              (all-< literal-nodenums dag-len))
                  :guard-hints (("Goal" :cases ((equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))) ;why is this :cases hint needed?
                                 :in-theory (e/d (car-becomes-nth-of-0
                                                           <-of-nth-when-all-<
                                                           ;FIND-VAR-AND-EXPR-TO-SUBST
                                                           ;NODENUM-OF-VAR-TO-SUBSTP
                                                           natp-of-lookup-equal-when-dag-variable-alistp
                                                           natp-of-cdr-of-assoc-equal-when-dag-variable-alistp)
                                                        (natp))))))
  (b* (((when (not (consp literal-nodenums))) ;; because var-okay-to-elim asks for the max literal nodenum
        (mv (erp-nil)
            nil ; no change
            literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (true-listp-vars (get-known-true-listp-vars literal-nodenums dag-array dag-len))
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
                         ((mv erp provedp literal-nodenums ;fixme could these ever be quoteps? if so, call handle-constant-disjuncts and return provedp?
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                          ;; ;this puts in the cons nest for the var everywhere it appears (fixme i guess nth of cons will then fire a lot..)
                          ;; this used to be accomplished by rewriting - yuck
                          (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              nodenum-of-var cons-nest-nodenum))
                         ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ((when provedp)
                          (er hard? 'eliminate-a-tuple "Tuple elimination proved the goal, which is not yet supported.")
                          (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         (- (cw ")~%")))
                      (mv (erp-nil)
                          t ;; changep is true
                          literal-nodenums
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          ;;(split-test-cases test-cases var new-vars) ;slow?
                          )))))))))

(defthm eliminate-a-tuple-return-type
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                ;;(consp literal-nodenums)
                ;(equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                ;;(not (mv-nth 0 (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
                )
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
             (implies (not erp)
                      (and (booleanp changep)
                           (all-natp new-literal-nodenums)
                           (true-listp new-literal-nodenums)
                           (<= (len new-literal-nodenums) (len literal-nodenums))
                           ;; (consp new-literal-nodenums)
                           (all-< new-literal-nodenums new-dag-len)
                           (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                           (<= dag-len new-dag-len)))))
  :hints (("Goal" :in-theory (e/d (eliminate-a-tuple natp-of-cdr-of-assoc-equal-when-dag-variable-alistp)
                                  (natp)))))

(defthm eliminate-a-tuple-return-type-corollary
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                ;;(consp literal-nodenums)
                ;(equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                ;;(not (mv-nth 0 (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
                )
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
             (declare (ignore changep new-literal-nodenums new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (and (not erp)
                           (<= bound new-dag-len)
                           (natp bound))
                      (and (pseudo-dag-arrayp 'dag-array new-dag-array bound)))))
  :hints (("Goal" :use (eliminate-a-tuple-return-type)
           :in-theory (disable eliminate-a-tuple-return-type))))

(defthm eliminate-a-tuple-return-type-corollary-linear
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                ;;(consp literal-nodenums)
                )
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
             (declare (ignore changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (not erp)
                      (<= dag-len new-dag-len))))
  :rule-classes :linear
  :hints (("Goal" :use (eliminate-a-tuple-return-type)
           :in-theory (disable eliminate-a-tuple-return-type))))

(defthm eliminate-a-tuple-return-type-2
  (implies (natp dag-len)
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
             (declare (ignore erp changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (natp new-dag-len)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (eliminate-a-tuple natp-of-cdr-of-assoc-equal-when-dag-variable-alistp)
                                  (natp)))))

(defthm eliminate-a-tuple-return-type-3
  (implies (natp dag-len)
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
             (declare (ignore erp changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (integerp new-dag-len)))
  :hints (("Goal" :in-theory (e/d (eliminate-a-tuple natp-of-cdr-of-assoc-equal-when-dag-variable-alistp)
                                  (natp)))))

(defthm eliminate-a-tuple-return-type-4
  (implies (true-listp literal-nodenums)
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
             (declare (ignore erp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (true-listp new-literal-nodenums)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (eliminate-a-tuple natp-of-cdr-of-assoc-equal-when-dag-variable-alistp)
                                  (natp)))))
