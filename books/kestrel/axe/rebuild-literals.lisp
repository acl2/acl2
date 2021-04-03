; Tools to rebuild DAGs while variable substitutions
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
(local (include-book "merge-sort-less-than-rules"))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system)) ;needed for reasoning about sort
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local
 ;; Disabled by default
 (defthmd acl2-numberp-when-integerp
   (implies (integerp x)
            (acl2-numberp x))))

;;;
;;; rebuild-nodes-with-var-subst-aux
;;;

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing the substitution to variable nodes indicated by TRANSLATION-ARRAY (which, as we go, also tracks changes to function call nodes that depend on those var nodes).
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; TODO: this could compute ground terms - but the caller would need to check for quoteps in the result
;; TODO: We could stop once we hit a node smaller than any node which is changed in the translation-array?  track the smallest node with a pending change.  no smaller node needs to be changed?
(defund rebuild-nodes-with-var-subst-aux (worklist ;nodenums, should be sorted
                                          translation-array ;maps each nodenum to nil (no change or not yet :examined) or a nodenum other than itself [or a quotep - no, not currently]
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
          ;; for termination: -- still needed?
          (not (and (mbt (array1p 'worklist-array worklist-array))
                    (mbt (all-natp worklist))
                    (mbt (all-< worklist (alen1 'worklist-array worklist-array))))))
      (mv (erp-nil) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((nodenum (first worklist))
           (expr (aref1 'dag-array dag-array nodenum)))
      (if (atom expr)
          ;;it's a variable, so either it was marked for replacement in the
          ;;initial translation array (and is still so marked), or it's not
          ;;being replaced
          (rebuild-nodes-with-var-subst-aux (rest worklist)
                                            translation-array ;; no change in either case
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            ;; We mark the node as "examined" so it doesn't get added again:
                                            (aset1 'worklist-array worklist-array nodenum :examined))
        (if (fquotep expr)
            ;;it's a constant (rare), so it's not being replaced (currently, but see todo below)
            (rebuild-nodes-with-var-subst-aux (rest worklist)
                                              ;;todo: i'd like to set nodenum to expr in this, to inline the constant, but that would cause translation-array to map nodes to things other than nodenums (which the callers would need to handle -- e.g., if a literal maps to a quotep):
                                              translation-array
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              ;; We mark the node as "examined" so it doesn't get added again:
                                              (aset1 'worklist-array worklist-array nodenum :examined))
          ;; it's a function call:
          (if (eq :examined (aref1 'worklist-array worklist-array nodenum))
              ;; The node has been examined, and since we are back to handling
              ;; it again, we know that its children have already been examined
              ;; and processed.  So now we can process this node:
              (let* ((args (dargs expr))
                     (new-args (maybe-translate-args args translation-array)))
                (if (not (equal args new-args)) ; since, if new-args=args (often), they should be eq, since maybe-translate-args calls cons-with-hint
                    ;; TODO: It would be nice to evaluate ground terms here,
                    ;; but that could cause translation-array to map nodes to
                    ;; quoteps (which the callers would need to handle -- e.g.,
                    ;; if a literal maps to a quotep).
                    ;; Something changed, so we have to add the new expr to the dag:
                    (b* (((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                          (add-function-call-expr-to-dag-array (ffn-symb expr) new-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ((when erp) (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                      (rebuild-nodes-with-var-subst-aux (rest worklist)
                                                        ;; Record what NODENUM was changed to:
                                                        (aset1 'translation-array translation-array nodenum new-nodenum)
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        worklist-array ; nodenum is already :examined
                                                        ))
                  ;; Args did not change, so no change to this node:
                  (rebuild-nodes-with-var-subst-aux (rest worklist) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)))
            ;; The node is not yet :examined, so we "expand" it. Its children
            ;; have not necessarily been processed, but if they've been
            ;; examined, they've been fully processed.
            (let* ((unexamined-args (get-unexamined-nodenum-args (dargs expr) worklist-array nil))
                   ;; TODO: Optimze the case where unexamined-args is nil?
                   ;; TODO: Maybe combine the sorting with get-unexamined-nodenum-args?  usually the number of nodenum args will be very small
                   (sorted-unexamined-args (merge-sort-< unexamined-args)))
              (rebuild-nodes-with-var-subst-aux (append sorted-unexamined-args worklist) ; we could perhaps save this append by making the worklist a list of lists, or we could combine this append with the merge-sort-<
                                                translation-array
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                ;; This node has now been examined:
                                                (aset1 'worklist-array worklist-array nodenum :examined)))))))))

(verify-guards rebuild-nodes-with-var-subst-aux :hints (("Goal" :in-theory (e/d (<-of-car-when-all-< dargp-of-car-when-all-natp
                                                                                      all-<=-when-all-<)
                                                                 (dargp
                                                                  dargp-less-than
                                                                  SORTEDP-<=)))))
(def-dag-builder-theorems
  (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst-aux))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst-aux))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
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
                                   (mv-nth '1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-with-var-subst-aux) (dargp)))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
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
                                           (mv-nth 1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))
                                           (mv-nth 3 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-with-var-subst-aux) (dargp)))))

;;;
;;; rebuild-nodes-with-var-subst
;;;

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing
;; the substitution indicated by TRANSLATION-ARRAY.
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where the result of rebuilding a
;; given node can be found by looking it up in the translation-array returned.
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; Smashes 'worklist-array.
(defund rebuild-nodes-with-var-subst (worklist ;should be sorted
                                      translation-array ;maps each nodenum to nil (no replacement, unless a child is to be replaced) or a nodenum (maybe the nodenum itself?) [or a quotep - no, not currently]
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
  (rebuild-nodes-with-var-subst-aux worklist
                                    translation-array
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    (make-empty-array 'worklist-array (alen1 'translation-array translation-array))))

(def-dag-builder-theorems
  (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
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

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-with-var-subst
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-with-var-subst
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst
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
                                   (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst
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
                                           (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                           (mv-nth 3 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

;;;
;;; rebuild-literals-with-substitution
;;;

;; Returns (mv erp literal-nodenums dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where the literal-nodenums are in
;; arbitrary order.
;; Smashes 'translation-array and 'worklist-array.
;ffixme can the literal-nodenums returned ever contain a quotep?
;this could compute ground terms - but the caller would need to check for quoteps in the result
;doesn't change any existing nodes in the dag (just builds new ones)
;; TODO: Consider making a version of this for prover depth 0 which rebuilds
;; the array from scratch (since we can change existing nodes when at depth 0).
(defund rebuild-literals-with-substitution (literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            nodenum-to-replace ; must be the nodenum of a var
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
       ;; Mark nodenum-to-replace to be replaced by new-nodenum:
       (translation-array (aset1 'translation-array translation-array nodenum-to-replace new-nodenum))
       ;; Rebuild all the literals, and their supporters, with the substitution applied:
       ((mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (rebuild-nodes-with-var-subst sorted-literal-nodenums ;; initial worklist
                                      translation-array
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((when erp) (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ;; Look up the possibly-new nodes that represent the literals:
       ((mv changed-literal-nodenums
            unchanged-literal-nodenums)
        (translate-literals literal-nodenums ;; could use sorted-literal-nodenums instead
                         translation-array
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
                          acl2-numberp-when-integerp
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
