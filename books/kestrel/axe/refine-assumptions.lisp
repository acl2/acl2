; Refining assumptions for better matching
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

;(include-book "all-dargp")
(include-book "kestrel/utilities/pseudo-termp" :dir :system) ;make local?
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
;(include-book "renaming-array")
;(include-book "axe-trees")
(include-book "merge-term-into-dag-array-basic") ;for merge-terms-into-dag-array-basic, depends on the basic evaluator
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;(local (in-theory (disable symbol-listp))) ; prevent inductions

;; like strip-cars but that one requires an alist
(defun map-ffn-symb (terms)
  (declare (xargs :guard (all-consp terms)))
  (if (atom terms)
      nil
    (cons (ffn-symb (first terms))
          (map-ffn-symb (rest terms)))))

;;;
;;; refining assumptions for matching (producing a list of terms)
;;;

;use this more?
(defund call-of-a-pred-except-not (term known-boolean-fns)
  (declare (xargs :guard (symbol-listp known-boolean-fns)))
  (and (consp term)
       (member-eq (ffn-symb term) known-boolean-fns)))

;; TODO: What if it contains lambdas but not at the top level (may be fine?)
;returns either the refined assumption (a term) or nil, meaning to drop this assumption
;fffixme what if it's a booland - should refine the parts and return several assumptions?
;the refined assumptions should not be quoteps or vars (might we ever want to assume a var?)?
;this could return an indication of when an assumption is known to be false (e.g., equality of two constants)?
(defund refine-assumption-for-matching (assumption known-boolean-fns)
  (declare (xargs :guard (and (pseudo-termp assumption)
                              (symbol-listp known-boolean-fns))))
  (if (atom assumption)
      ;;fixme an assumption that is a var can be turned into (not (equal nil <var>)) ?
      (prog2$ (cw "!! refine-assumption-for-matching is dropping weird assumption ~x0~%" assumption) ;hard error if it's not a var?
              nil)
    (let ((fn (ffn-symb assumption)))
      (if (eq 'quote fn) ;can this happen?
          (prog2$ (cw "!! refine-assumption-for-matching is dropping quotep assumption ~x0~%" assumption)
                  nil)
        (if (consp fn)
            (prog2$ (cw "!! refine-assumption-for-matching is dropping assumption ~x0, which is a lambda application~%" assumption)
                    nil)
          (if (not (eq 'equal fn))
              ;;can't refine this assumption (fixme what about other equivalence relations?):
              assumption
            ;;it's a call of equal:
            ;;refine (equal <predicate> 't) to <predicate>:
            (if (and (equal (farg2 assumption) *t*)
                     (call-of-a-pred-except-not (farg1 assumption) known-boolean-fns)) ;why are we excluding not here and elsewhere?
                (farg1 assumption)
              ;;refine (equal 't <predicate>) to <predicate>:
              (if (and (equal (farg1 assumption) *t*)
                       (call-of-a-pred-except-not (farg2 assumption) known-boolean-fns))
                  (farg2 assumption)
                ;;refine (equal <predicate> 'nil) to (not <predicate>):
                (if (and (equal (farg2 assumption) *nil*)
                         (call-of-a-pred-except-not (farg1 assumption) known-boolean-fns) ;could drop this check!
                         )
                    `(not ,(farg1 assumption))
                  ;;refine (equal 'nil <predicate>) to (not <predicate>):
                  (if (and (equal (farg1 assumption) *nil*)
                           (call-of-a-pred-except-not (farg2 assumption) known-boolean-fns) ;could drop this check!
                           )
                      `(not ,(farg2 assumption))
                    (if (quotep (farg2 assumption))
                        (if (quotep (farg1 assumption))
                            ;;weird to have the equality of two constants (ffixme check for any ground term that we can eval?)
                            ;;if they are different constants, perhaps this should throw an error or print a more visible message?!
                            (prog2$ (cw "!! refine-assumption-for-matching is dropping weird assumption ~x0~%" assumption)
                                    nil)
                          ;; refine (equal <non-constant> <constant>) to (equal <constant> <non-constant>):
                          ;; putting the constant first matches our normal form for rules such as bvchop-subst-constant:
                          `(equal ,(farg2 assumption) ,(farg1 assumption)))
                      ;;can't refine this assumption:
                      assumption)))))))))))

(defthm pseudo-termp-of-refine-assumption-for-matching
  (implies (pseudo-termp assumption)
           (pseudo-termp (refine-assumption-for-matching assumption known-boolean-fns)))
  :hints (("Goal" :in-theory (enable refine-assumption-for-matching))))

(defthm symbolp-of-car-of-refine-assumption-for-matching
  (implies (and (pseudo-termp assumption)
                (symbol-listp known-boolean-fns))
           (symbolp (car (refine-assumption-for-matching assumption known-boolean-fns))))
  :hints (("Goal" :in-theory (enable refine-assumption-for-matching call-of-a-pred-except-not
                                     symbol-listp ;todo
                                     ))))

(defthm consp-of-refine-assumption-for-matching
  (implies (and (pseudo-termp assumption)
                )
           (iff (consp (refine-assumption-for-matching assumption known-boolean-fns))
                (refine-assumption-for-matching assumption known-boolean-fns)))
  :hints (("Goal" :in-theory (enable refine-assumption-for-matching call-of-a-pred-except-not))))

;returns a list of terms, each of which should be a function call term
(defund refine-assumptions-for-matching (assumptions known-boolean-fns acc)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (symbol-listp known-boolean-fns))))
  (if (endp assumptions)
      acc
    (let* ((assumption (first assumptions))
           (refined-assumption (refine-assumption-for-matching assumption known-boolean-fns)))
      (refine-assumptions-for-matching (rest assumptions)
                                       known-boolean-fns
                                       (if refined-assumption
                                           (cons refined-assumption acc)
                                         acc)))))

(defthm pseudo-term-listp-of-refine-assumptions-for-matching
  (implies (and (pseudo-term-listp assumptions)
                (pseudo-term-listp acc))
           (pseudo-term-listp (refine-assumptions-for-matching assumptions known-boolean-fns acc)))
  :hints (("Goal" :in-theory (enable refine-assumptions-for-matching))))

(defthm symbol-listp-of-map-ffn-symb-of-refine-assumptions-for-matching
  (implies (and (pseudo-term-listp assumptions)
                (symbol-listp (map-ffn-symb acc))
                (symbol-listp known-boolean-fns))
           (symbol-listp (map-ffn-symb (refine-assumptions-for-matching assumptions known-boolean-fns acc))))
  :hints (("Goal" :in-theory (enable refine-assumptions-for-matching))))

(defthm all-consp-of-refine-assumptions-for-matching
  (implies (and (pseudo-term-listp assumptions)
                (all-consp acc))
           (all-consp (refine-assumptions-for-matching assumptions known-boolean-fns acc)))
  :hints (("Goal" :in-theory (enable refine-assumptions-for-matching))))

(local (in-theory (disable wf-dagp wf-dagp-expander)))

;;;
;;; add-refined-assumptions-to-dag-array
;;;

;; For each of the ASSUMPTIONS, adds its args to the dag-array.  Returns a list of all the fns applied to their corresponding args (added to the array).
;; Returns (mv erp refined-assumption-exprs ;function calls applied to quoteps / nodenums in dag-array
;;             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;call this "add-fn-call-terms-to-dag-array"? well, that might be assumed to return a list of nodenums, but this doesn't...
(defund add-refined-assumptions-to-dag-array (assumptions ;terms (must be function calls, not lambdas)
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              dag-array-name
                                              dag-parent-array-name
                                              acc)
  ;;todo: strengthen:
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (all-consp assumptions) ; error below if any is a quotep
                              (symbol-listp (map-ffn-symb assumptions)) ; no lambdas
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
                  :guard-hints (("Goal" :expand ((pseudo-termp (car assumptions))
                                                 (pseudo-term-listp assumptions))))))
  (if (endp assumptions)
      (mv (erp-nil) acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let ((assumption (first assumptions)))
      (if (eq 'quote (ffn-symb assumption)) ; todo: prove this never happens when we call this function on the output of refine-assumptions-for-matching
          (prog2$ (er hard? 'add-refined-assumptions-to-dag-array "Constant assumption encountered.")
                  (mv (erp-t) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
        (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          ;; TODO: This can do evaluation.  shall we avoid that?
          (merge-terms-into-dag-array-basic (fargs assumption)
                                            nil ;var-replacement-alist
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            dag-array-name dag-parent-array-name
                                            nil ;interpreted-function-alist
                                            )
          (if erp
              (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (add-refined-assumptions-to-dag-array (rest assumptions)
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  dag-array-name
                                                  dag-parent-array-name
                                                  (cons (cons (ffn-symb assumption) nodenums-or-quoteps)
                                                        acc))))))))
;move?
(defforall all-dag-function-call-exprp (items) (dag-function-call-exprp items)
  :declares ((type t items)))

(defthm all-dag-function-call-exprp-of-mv-nth-1-of-add-refined-assumptions-to-dag-array
  (implies (and (pseudo-term-listp assumptions)
                (all-consp assumptions)                 ;todo: what if quoted?
                (symbol-listp (map-ffn-symb assumptions)) ;strengthen?
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;;no error:
                (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)))
                (all-dag-function-call-exprp acc)
                )
           (all-dag-function-call-exprp (mv-nth 1 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
  :hints (("Goal" :expand (pseudo-termp (car assumptions))
           :in-theory (enable pseudo-termp add-refined-assumptions-to-dag-array symbol-listp))))

;; (defthm axe-tree-listp-of-mv-nth-1-of-add-refined-assumptions-to-dag-array
;;   (implies (and (pseudo-term-listp assumptions)
;;                 (all-consp assumptions)                 ;todo: what if quoted?
;;                 (symbol-listp (map-ffn-symb assumptions)) ;strengthen?
;;                 (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
;;                 ;;no error:
;;                 (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)))
;;                 (axe-tree-listp acc)
;;                 )
;;            (axe-tree-listp (mv-nth 1 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
;;   :hints (("Goal" :expand (pseudo-termp (car assumptions))
;;            :in-theory (enable pseudo-termp add-refined-assumptions-to-dag-array symbol-listp))))

(defthm true-listp-of-mv-nth-1-of-add-refined-assumptions-to-dag-array
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
  :hints (("Goal" :expand (pseudo-termp (car assumptions))
           :in-theory (enable pseudo-termp add-refined-assumptions-to-dag-array))))

(defthm natp-of-mv-nth-3-of-add-refined-assumptions-to-dag-array
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
  :hints (("Goal" :in-theory (enable add-refined-assumptions-to-dag-array))))

(defthm wf-dagp-of-add-refined-assumptions-to-dag-array
  (implies (and (pseudo-term-listp assumptions)
                (all-consp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; no error:
                (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
           (mv-let (erp refined-assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)
             (declare (ignore erp refined-assumptions))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :expand ((pseudo-term-listp assumptions)
                           (pseudo-termp (car assumptions)))
           :in-theory (enable add-refined-assumptions-to-dag-array))))

(defthm bounded-dag-expr-listp-of-add-refined-assumptions-to-dag-array
  (implies (and (pseudo-term-listp assumptions)
                (all-consp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; no error:
                (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)))
                ;(all-dag-exprp acc)
                (bounded-dag-expr-listp dag-len acc)
                (symbol-listp (map-ffn-symb assumptions))
                )
           (mv-let (erp refined-assumption-exprs dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)
             (declare (ignore erp dag-array dag-parent-array dag-constant-alist dag-variable-alist))
             (bounded-dag-expr-listp dag-len refined-assumption-exprs)))
  :hints (("Goal" :expand (;(pseudo-term-listp assumptions)
                           (pseudo-termp (car assumptions))
                           )
           :in-theory (enable add-refined-assumptions-to-dag-array))))
