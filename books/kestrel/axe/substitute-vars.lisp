; Substituting for a variable in the Axe Prover
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

(include-book "rebuild-nodes")
(include-book "supporting-nodes")
(include-book "crunch-dag2")
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))

;; See also substitute-vars2.lisp

;move
(defthm not-<-of-+-1-of-maxelem
 (implies (and (all-< x y)
               (integerp y)
               (all-integerp x)
               (consp x))
          (not (< y (+ 1 (maxelem x)))))
 :hints (("Goal" :in-theory (enable all-< maxelem))))

(local
 ;; disabled by default
 (defthmd rationalp-when-natp
   (implies (natp x)
            (rationalp x))))

;move
(defthm consp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple-iff
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                (natp n))
           (iff (consp (dargs (aref1 dag-array-name dag-array n)))
                (dargs (aref1 dag-array-name dag-array n)))))

;decides whether we should substitute (is it the nodenum of a var, and is it equated to a term that doesn't include itself?)
;returns (mv substp var nodenum-of-var)
;equated-thing is a quotep or nodenum
;todo: don't return nodenum-or-quotep?
(defund nodenum-of-var-to-substp (nodenum-or-quotep equated-thing dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than nodenum-or-quotep dag-len)
                              (dargp-less-than equated-thing dag-len)))
           (ignore dag-len))
  (if (and (atom nodenum-or-quotep) ;ensure it's a nodenum
           (not (consp equated-thing)) ; an equality of a var and a constant should be used when rewriting.. (fixme allow this, to get rid of var=const when var appears nowhere else)
           )
      (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
        (if (and (symbolp expr) ;must be a variable
                 ;;helps prevent loops?:
                 ;; TODO: Consider using a version of supporters-of-node that uses a worklist instead of walking over every node <= to the node of interest. See vars-that-support-dag-node.
                 ;; Also, we really only need supporting vars, not all suporters
                 (if (member nodenum-or-quotep (supporters-of-node equated-thing 'dag-array dag-array 'tag-array-for-supporters))
                     (prog2$ (cw "Refusing to substitute for ~x0 because it is equated to something involving itself !!~%" expr) ;; todo: print the terms involved?
                             nil)
                   t))
            (mv t expr nodenum-or-quotep)
          (mv nil nil nil)))
    (mv nil nil nil)))

;;;
;;; find-var-and-expr-to-subst
;;;

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
                (dargp rhs)
                (dargp lhs))
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
                (dargp rhs)
                (dargp lhs)
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

;;;
;;; check-for-var-subst-literal
;;;

;; Returns (mv foundp var nodenum-of-var nodenum-or-quotep-to-put-in).
;; nodenum-or-quotep-to-put-in may now always be a nodenum?
(defund check-for-var-subst-literal (literal-nodenum dag-array dag-len)
  (declare (xargs :guard (and (natp literal-nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< literal-nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (enable CONSP-OF-CDR)))
                  ))
  (let ((expr (aref1 'dag-array dag-array literal-nodenum)))
    ;; we seek an expr of the form (not <nodenum>)
    (if (not (and (call-of 'not expr)
                  (consp (dargs expr))
                  (integerp (darg1 expr))))
        (mv nil nil nil nil) ;fail
      (let ((non-nil-expr (aref1 'dag-array dag-array (darg1 expr)))) ;;we seek a NON-NIL-EXPR of the form (equal <nodenum-of-var> <thing>) or vice-versa
        (if (not (and (call-of 'equal non-nil-expr)
                      (consp (cdr (dargs non-nil-expr)))))
            (mv nil nil nil nil) ;fail
          (find-var-and-expr-to-subst (darg1 non-nil-expr) (darg2 non-nil-expr) dag-array dag-len) ;this is what prevents loops
          )))))

;;;
;;; substitute-a-var
;;;

;; Searches through literal-nodenums for a (negated) equality involving a variable (recall that a literal can be safely assumed false when rewriting other literals).
;; Requires that the variable is equated to some term not involving itself (to prevent loops).
;; If such a (negated) equality is found, it is used to substitute in all the other literals.  The literal representing the equality is then dropped, eliminating that variable from the DAG.
;; Returns (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;fixme could this ever transform a literal into a constant?
;; TODO: Consider substituting multiple variables at once.
;; Doesn't change any existing nodes in the dag (just builds new ones).
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
                                                         nodenum-of-var-to-substp
                                                         consp-of-cdr)
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
        (b* (((when (consp nodenum-or-quotep-to-put-in)) ;tests for quotep - always false?
              (prog2$ (er hard? 'substitute-a-var "Surprised to see a var equated to a constant") ;fixme print more..
                      (mv (erp-t) nil all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
             (- (and ;; print ;; (or (eq t print) (eq :verbose print))
                 ;; (and print (cw "~%(Using ~x0 to replace ~x1 (~x2 -> ~x3).~%" literal-nodenum var nodenum-of-var nodenum-or-quotep-to-put-in))
                 (and print (cw "~%(Using ~x0 to replace ~x1, which is ~x2.~%" literal-nodenum var (aref1 'dag-array dag-array nodenum-or-quotep-to-put-in)))
                 ;; (progn$ (cw "~%(Substituting to replace ~x0 (node ~x1) with:~%" var nodenum-of-var)
                 ;;         (if (quotep nodenum-or-quotep-to-put-in) ;always false?
                 ;;             (cw "~x0" nodenum-or-quotep-to-put-in)
                 ;;           (if print
                 ;;               (print-dag-only-supporters 'dag-array dag-array nodenum-or-quotep-to-put-in)
                 ;;             (cw ":elided"))))
                 ))
             ((mv erp literal-nodenums ;fixme could these ever be quoteps?
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                  )
              ;; TODO: Combine these 2 passes through the literals (the remove and the rebuild):
              (rebuild-literals-with-substitution (remove literal-nodenum all-literal-nodenums) ;remove the equality we used ;make use of the fact that the item appears only once?
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  nodenum-of-var
                                                  nodenum-or-quotep-to-put-in ;known to be a nodenum
                                                  ))
             ((when erp) (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
             ;; todo: avoid the call of len (compute it during the pass through the literals above?):
             (- (and print (cw " ~x0 literals left, dag len is ~x1)~%" (len literal-nodenums) dag-len))))
          (mv (erp-nil) t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))

;; not phrased as a equality since multiple copies of the found literal may be removed
(defthm len-of-mv-nth2-of-substitute-a-var
  (implies (and (mv-nth 1 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                (subsetp-equal literal-nodenums all-literal-nodenums))
           (< (len (mv-nth 2 (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
              (len all-literal-nodenums)))
  :hints (("Goal" :in-theory (enable substitute-a-var))))

;;for the def-dag-builder-theorems just below (todo: should not be needed?):
(local (in-theory (enable check-for-var-subst-literal consp-of-cdr)))

(def-dag-builder-theorems
  (substitute-a-var literal-nodenums all-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
  (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp literal-nodenums)
         (all-< literal-nodenums dag-len)
         (nat-listp all-literal-nodenums)
         (all-< all-literal-nodenums dag-len))
  ;; TODO: Why doesn't this work without the in-theory event above?
  ;; :hints (("Goal" :in-theory (enable substitute-a-var
  ;;                                    check-for-var-subst-literal)))
  )

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

;; Repeatedly get rid of vars by substitution.
;; Returns (mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;; Doesn't change any nodes if prover-depth > 0.
(defund substitute-vars (literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth
                                          initial-dag-len ;; only used for deciding when to crunch
                                          changep-acc)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (natp prover-depth)
                              (posp initial-dag-len)
                              (booleanp changep-acc))
                  :measure (len literal-nodenums)
                  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))))
  (b* (;; Try to subst a var.  TODO: Allow this to evaluate ground terms that arise when substituting.
       ((mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
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
                     (> (/ dag-len initial-dag-len)
                        ;; todo: what is the best threshold ratio to use here?:
                        10)) ;; crunching is less important now that we substitute first with lits that were just rebuilt
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
        (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len t)))))

(defthm substitute-vars-return-type
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp prover-depth)
                (natp num)
                (booleanp changep-acc))
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (implies (not erp)
                      (and (booleanp changep)
                           (nat-listp new-literal-nodenums)
                           (all-natp new-literal-nodenums) ;follows from the above
                           (true-listp new-literal-nodenums) ;follows from the above
                           (all-< new-literal-nodenums new-dag-len)
                           (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                           (implies (< 0 prover-depth)
                                    (<= dag-len new-dag-len))))))
  :hints (("Goal" :in-theory (enable substitute-vars))))

(defthm substitute-vars-return-type-corollary
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp prover-depth)
                (natp num)
                (booleanp changep-acc))
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (declare (ignore changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (not erp)
                      (implies (< 0 prover-depth)
                               (<= dag-len new-dag-len)))))
  :rule-classes :linear
  :hints (("Goal" :use (substitute-vars-return-type)
           :in-theory (disable substitute-vars-return-type))))

(defthm substitute-vars-return-type-2
  (implies (true-listp literal-nodenums)
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (declare (ignore erp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (true-listp new-literal-nodenums)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable substitute-vars))))

(defthm substitute-vars-return-type-3
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp prover-depth)
                (natp num)
                (booleanp changep-acc))
           (mv-let (erp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (declare (ignore changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (not erp)
                      (natp new-dag-len))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (substitute-vars) (natp)))))
