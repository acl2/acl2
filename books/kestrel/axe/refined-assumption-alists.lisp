; An alist that stores assumptions
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

(include-book "all-dargp")
(include-book "kestrel/utilities/pseudo-termp" :dir :system) ;make local?
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "renaming-array")
(include-book "merge-term-into-dag-array-basic") ;for merge-terms-into-dag-array-basic, depends on the basic evaluator
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;; Usage (see refine-assumptions-and-add-to-dag-array):
;;;
;;; 1. Call refine-assumptions-for-matching to produce a list of terms.
;;;
;;; 2. Call add-refined-assumptions-to-dag-array to add the args of the refined
;;;    assumptions to the dag-array, yielding a list of function call axe-trees.
;;;
;;; 3. Call make-refined-assumption-alist on the resulting axe-trees.

;; See also the comment "How we use the refined-assumption-alist" in make-rewriter-simple.lisp

;move
(defthm all-bounded-axe-treep-when-all-dargp
  (implies (all-dargp items)
           (equal (all-bounded-axe-treep items bound)
                  (all-dargp-less-than items bound)))
  :hints (("Goal" :expand ((bounded-axe-treep (car items) bound)
                           (all-bounded-axe-treep items bound))
           :in-theory (enable all-bounded-axe-treep all-dargp-less-than))))

(defthm true-listp-of-dargs-when-dag-exprp0
  (implies (and (dag-exprp0 expr)
                ;; (consp expr)
                ;; (not (equal 'quote (car expr)))
                )
           (true-listp (dargs expr)))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

(local (in-theory (disable symbol-listp))) ; prevent inductions

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

(defthm pseudo-term-listp-of-refine-assumption-for-matching
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

(defthm symbol-listp-of-strip-cars-of-refine-assumptions-for-matching
  (implies (and (symbol-listp known-boolean-fns)
                (pseudo-term-listp assumptions)
                (symbol-listp (strip-cars acc)))
           (symbol-listp (strip-cars (refine-assumptions-for-matching assumptions known-boolean-fns acc))))
  :hints (("Goal" :in-theory (enable refine-assumptions-for-matching symbol-listp))))

(defthm all-consp-of-refine-assumptions-for-matching
  (implies (and (pseudo-term-listp assumptions)
                (all-consp acc))
           (all-consp (refine-assumptions-for-matching assumptions known-boolean-fns acc)))
  :hints (("Goal" :in-theory (enable refine-assumptions-for-matching))))

;;;
;;; refined-assumption-alists
;;;

(defun dargp-listp (items)
  (declare (xargs :guard t))
  (and (true-listp items)
       (all-dargp items)))

(defforall all-dargp-listp (items) (dargp-listp items)
  :declares ((type t items)))

(defun dargp-list-listp (items)
  (declare (xargs :guard t))
  (and (true-listp items)
       (all-dargp-listp items)))

;; A "refined-assumption-alist" is an efficient way to store a list of
;; axe-trees, all of which are function calls applied to args that are nodenums
;; / quoteps.  We use "term indexing": the alist maps each topmost function to
;; a list of arg-lists (one for each call of fn in the list).

;could add more checks to this
(defun refined-assumption-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symbolp (car entry)) ;; should lambdas be allowed?
           ;; (not (eq 'quote (car entry))) ;; TODO: Uncomment
           (dargp-list-listp (cdr entry)) ;(true-listp (cdr entry)) ; check that each member of (cdr entry) is a list of nodenum/quoteps
           (refined-assumption-alistp (cdr alist))))))

(defthm symbol-alistp-when-refined-assumption-alistp-cheap
  (implies (refined-assumption-alistp acc)
           (symbol-alistp acc))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm true-listp-of-lookup-equal-when-refined-assumption-alistp-cheap
  (implies (refined-assumption-alistp alist)
           (true-listp (lookup-equal sym alist)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;
;;; bounded refined-assumption-alists
;;;

(defun dargp-less-than-listp (items dag-len)
  (declare (xargs :guard (natp dag-len)))
  (if (atom items)
      (null items)
    (and (dargp-less-than (first items) dag-len)
         (dargp-less-than-listp (rest items) dag-len))))

(defthm dargp-less-than-listp-rewrite
  (equal (dargp-less-than-listp items bound)
         (and (all-dargp-less-than items bound)
              (true-listp items)))
  :hints (("Goal" :in-theory (enable dargp-less-than-listp))))

(defthm dargp-listp-when-dargp-less-than-listp
  (implies (dargp-less-than-listp items dag-len)
           (dargp-listp items)))

(defund dargp-less-than-list-listp (items dag-len)
  (declare (xargs :guard (natp dag-len)))
  (if (atom items)
      (null items)
    (and (dargp-less-than-listp (first items) dag-len)
         (dargp-less-than-list-listp (rest items) dag-len))))

;; (defthm dargp-less-than-list-listp-rewrite
;;   (equal (dargp-less-than-list-listp items bound)
;;          (and (all-all-dargp-less-than items bound)
;;               (true-listp items)))
;;   :hints (("Goal" :in-theory (enable dargp-less-than-listp))))

(defthm dargp-less-than-list-listp-forward-to-true-listp
  (implies (dargp-less-than-list-listp items dag-len)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

(defthm dargp-less-than-list-listp-of-nil
  (dargp-less-than-list-listp nil dag-len)
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

(defthm dargp-less-than-list-listp-of-cons
  (equal (dargp-less-than-list-listp (cons a x) dag-len)
         (and (dargp-less-than-listp a dag-len)
              (dargp-less-than-list-listp x dag-len)))
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

(defthm dargp-less-than-list-listp-monotone
  (implies (and (dargp-less-than-list-listp alist bound2)
                (<= bound2 bound))
           (dargp-less-than-list-listp alist bound))
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

(defthm all-dargp-less-than-of-car
  (implies (dargp-less-than-list-listp items dag-len)
           (all-dargp-less-than (car items) dag-len))
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

(defthm dargp-less-than-list-listp-of-cdr
  (implies (dargp-less-than-list-listp items dag-len)
           (dargp-less-than-list-listp (cdr items) dag-len))
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

(defthm dargp-list-listp-when-dargp-less-than-list-listp
  (implies (dargp-less-than-list-listp items bound)
           (dargp-list-listp items))
  :hints (("Goal" :in-theory (enable dargp-less-than-list-listp))))

;;;
;;; bounded-refined-assumption-alistp
;;;

(defund bounded-refined-assumption-alistp (alist dag-len)
  (declare (xargs :guard (natp dag-len)))
  (if (atom alist)
      (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symbolp (car entry)) ;; should lambdas be allowed?
           (dargp-less-than-list-listp (cdr entry) dag-len)
           (bounded-refined-assumption-alistp (cdr alist) dag-len)))))

(defthm refined-assumption-alistp-when-bounded-refined-assumption-alistp
  (implies (bounded-refined-assumption-alistp alist dag-len)
           (refined-assumption-alistp alist))
  :hints (("Goal" :in-theory (e/d (bounded-refined-assumption-alistp)
                                  (dargp-list-listp)))))

(defthm bounded-refined-assumption-alistp-monotone
  (implies (and (bounded-refined-assumption-alistp alist bound2)
                (<= bound2 bound))
           (bounded-refined-assumption-alistp alist bound))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp))))

(defthm bounded-refined-assumption-alistp-of-uniquify-alist-eq-aux
  (implies (and (bounded-refined-assumption-alistp alist bound)
                (bounded-refined-assumption-alistp acc bound))
           (bounded-refined-assumption-alistp (uniquify-alist-eq-aux alist acc) bound))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp uniquify-alist-eq-aux))))

(defthm dargp-less-than-list-listp-of-lookup-equal-when-bounded-refined-assumption-alistp
  (implies (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
           (dargp-less-than-list-listp (lookup-equal fn refined-assumption-alist)
                                                  dag-len))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp lookup-equal assoc-equal))))

(defthm bounded-refined-assumption-alistp-forward-to-symbol-alistp
  (implies (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
           (symbol-alistp refined-assumption-alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp))))

;does not check that the nodenums are not too big
;todo: replace?  just use DAG-FUNCTION-CALL-EXPRP?
;a kind of axe-tree
(defund weak-dag-fun-call-exprp (expr)
  (declare (xargs :guard t))
  (and (consp expr)
       (symbolp (ffn-symb expr)) ;disallows lambdas
       (not (eq 'quote (ffn-symb expr)))
       (dargp-listp (fargs expr))))

(defthm weak-dag-fun-call-exprp-forward-to-true-listp
  (implies (weak-dag-fun-call-exprp expr)
           (true-listp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable weak-dag-fun-call-exprp))))

(defthm weak-dag-fun-call-exprp-of-cons
  (equal (weak-dag-fun-call-exprp (cons fn args))
         (and (symbolp fn)
              (not (eq 'quote fn))
              (dargp-listp args)))
  :hints (("Goal" :in-theory (enable weak-dag-fun-call-exprp))))

(defforall all-weak-dag-fun-call-exprp (items) (weak-dag-fun-call-exprp items)
  :declares ((type t items)))

(defthm all-dargp-listp-of-lookup-equal
  (implies (refined-assumption-alistp alist)
           (all-dargp-listp (lookup-equal fn alist))))

(defthm refined-assumption-alistp-of-uniquify-alist-eq-aux
  (implies (and (refined-assumption-alistp acc)
                (refined-assumption-alistp alist))
           (refined-assumption-alistp (uniquify-alist-eq-aux alist acc))))

;the exprs are fn calls applied to nodenums / quoteps
(defund extend-refined-assumption-alist (exprs acc)
  (declare (xargs :guard (and (true-listp exprs)
                              (all-weak-dag-fun-call-exprp exprs)
                              (refined-assumption-alistp acc))))
  (if (endp exprs)
      (uniquify-alist-eq acc)
    (b* ((expr (first exprs))
         (fn (ffn-symb expr))
         ((when (not (symbolp fn)))
          (er hard? 'extend-refined-assumption-alist "Bad assumption (possibly a lambda?): ~x0." expr))
         (args (fargs expr))
         (arg-lists-for-fn (lookup-eq fn acc))
         (new-arg-lists-for-fn (cons args arg-lists-for-fn)))
        (extend-refined-assumption-alist (rest exprs)
                                         (acons-fast fn new-arg-lists-for-fn acc)))))

(defthm refined-assumption-alistp-of-extend-refined-assumption-alist
  (implies (and (refined-assumption-alistp acc)
                (all-weak-dag-fun-call-exprp exprs))
           (refined-assumption-alistp (extend-refined-assumption-alist exprs acc)))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist
  (implies (and (bounded-refined-assumption-alistp acc bound)
                (all-weak-dag-fun-call-exprp exprs)
                (all-bounded-axe-treep exprs bound))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist exprs acc) bound))
  :hints (("Goal" :expand ((all-bounded-axe-treep exprs bound)
                           (bounded-axe-treep (car exprs) bound)
                           (all-weak-dag-fun-call-exprp exprs))
           :in-theory (enable bounded-refined-assumption-alistp extend-refined-assumption-alist
                              weak-dag-fun-call-exprp))))

(defund make-refined-assumption-alist (exprs)
  (declare (xargs :guard (and (true-listp exprs)
                              (all-weak-dag-fun-call-exprp exprs))))
  (extend-refined-assumption-alist exprs nil))

(defthm refined-assumption-alistp-of-make-refined-assumption-alist
  (implies (all-weak-dag-fun-call-exprp exprs)
           (refined-assumption-alistp (make-refined-assumption-alist exprs)))
  :hints (("Goal" :in-theory (enable make-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-of-make-refined-assumption-alist
  (implies (and (all-weak-dag-fun-call-exprp exprs)
                (all-bounded-axe-treep exprs bound))
           (bounded-refined-assumption-alistp (make-refined-assumption-alist exprs) bound))
  :hints (("Goal" :in-theory (enable make-refined-assumption-alist
                                     bounded-refined-assumption-alistp))))

;;;
;;; nodenum-equal-to-refined-assumptionp
;;;

;; TODO: Just call member-equal and remove the p from this name?
(defund nodenum-equal-to-refined-assumptionp (nodenum refined-assumption-alist dag-array)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                              (refined-assumption-alistp refined-assumption-alist))))
  (let* ((expr (aref1 'dag-array dag-array nodenum)))
    (and (consp expr) ;refined assumptions must be function calls
         (let ((fn (ffn-symb expr)))
           (and (not (eq 'quote fn))
                (let ((arglists-for-fn (lookup-eq fn refined-assumption-alist)))
                  (memberp (dargs expr) arglists-for-fn)))))))



;; ;the assumptions are fn calls applied to nodenums/quoteps
;; (defun fixup-refined-assumptions (refined-assumptions renaming-array-name renaming-array acc)
;;   (if (endp refined-assumptions)
;;       acc
;;     (let* ((assumption (first refined-assumptions))
;;            (fn (ffn-symb assumption))
;;            (args (fargs assumption))
;;            (fixed-up-args (rename-args args renaming-array-name renaming-array))
;;            (fixed-up-assumption (cons fn fixed-up-args))
;;            )
;;       (fixup-refined-assumptions (rest refined-assumptions)
;;                                  renaming-array-name
;;                                  renaming-array
;;                                  (cons fixed-up-assumption
;;                                        acc)))))

(defun fixup-refined-assumption-arglists (arg-lists renaming-array-name renaming-array acc)
  (if (endp arg-lists)
      acc
    (let* ((arg-list (first arg-lists))
;           (fn (ffn-symb assumption))
 ;          (args (fargs assumption))
           (fixed-up-arg-list (rename-args arg-list renaming-array-name renaming-array))
;           (fixed-up-assumption (cons fn fixed-up-args))
           )
      (fixup-refined-assumption-arglists (rest arg-lists)
                                         renaming-array-name
                                         renaming-array
                                         (cons fixed-up-arg-list
                                               acc)))))

(defun fixup-refined-assumption-alist (refined-assumption-alist renaming-array-name renaming-array acc)
  (if (endp refined-assumption-alist)
      acc
    (let* ((entry (first refined-assumption-alist))
           (fn (car entry))
           (arg-lists (cdr entry))
           (fixed-up-arg-lists (fixup-refined-assumption-arglists arg-lists renaming-array-name renaming-array nil)))
      (fixup-refined-assumption-alist (rest refined-assumption-alist)
                                      renaming-array-name
                                      renaming-array
                                      (acons-fast fn fixed-up-arg-lists acc)))))

;;;
;;; decoding refined-assumption-alists (only used to implement WORK-HARD)
;;;

;see cons-onto-all
(defun add-fn-calls (fn arg-lists acc)
  (declare (xargs :guard (true-listp arg-lists)))
  (if (endp arg-lists)
      acc
    (add-fn-calls fn
                  (rest arg-lists)
                  (cons (cons fn (first arg-lists)) acc))))

(defun decode-refined-assumption-alist-aux (refined-assumption-alist acc)
  (declare (xargs :guard (refined-assumption-alistp refined-assumption-alist)))
  (if (endp refined-assumption-alist)
      acc
    (let* ((entry (car refined-assumption-alist))
           (fn (car entry))
           (arg-lists (cdr entry)))
      (decode-refined-assumption-alist-aux (cdr refined-assumption-alist)
                                           (add-fn-calls fn arg-lists acc)))))

;turns refined-assumption-alist back into the equivalent list of axe-trees
;; todo: prove return type
(defun decode-refined-assumption-alist (refined-assumption-alist)
  (declare (xargs :guard (refined-assumption-alistp refined-assumption-alist)))
  (decode-refined-assumption-alist-aux refined-assumption-alist nil))


(local (in-theory (disable wf-dagp wf-dagp-expander)))

;; For each of the ASSUMPTIONS, adds its args to the dag-array.  Returns a list of all the the fns applied to their corresponding args (added to the array).
;; Returns (mv erp refined-assumptions ;function calls applied to quoteps / nodenums in dag-array
;;             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;call this "add-fn-call-terms-to-dag-array"? well, that might be assumed to return a list of nodenums, but this doesn't...
(defund add-refined-assumptions-to-dag-array (assumptions ;terms (must be function calls)
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             dag-array-name
                                             dag-parent-array-name
                                             acc)
  ;;todo: strengthen:
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (all-consp assumptions) ;todo: what if quoted?
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
                  :guard-hints (("Goal" :expand ((pseudo-termp (car assumptions))
                                                 (pseudo-term-listp assumptions))))))
  (if (endp assumptions)
      (mv (erp-nil) acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let ((assumption (first assumptions)))
      (if (eq 'quote (ffn-symb assumption))
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

(defthm all-weak-dag-fun-call-exprp-of-mv-nth-1-of-add-refined-assumptions-to-dag-array
  (implies (and (pseudo-term-listp assumptions)
                (all-consp assumptions)                 ;todo: what if quoted?
                (symbol-listp (strip-cars assumptions)) ;strengthen?
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;;no error:
                (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)))
                (all-weak-dag-fun-call-exprp acc)
                )
           (all-weak-dag-fun-call-exprp (mv-nth 1 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
  :hints (("Goal" :expand (pseudo-termp (car assumptions))
           :in-theory (enable pseudo-termp add-refined-assumptions-to-dag-array symbol-listp))))

(defthm all-axe-treep-of-mv-nth-1-of-add-refined-assumptions-to-dag-array
  (implies (and (pseudo-term-listp assumptions)
                (all-consp assumptions)                 ;todo: what if quoted?
                (symbol-listp (strip-cars assumptions)) ;strengthen?
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;;no error:
                (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)))
                (all-axe-treep acc)
                )
           (all-axe-treep (mv-nth 1 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc))))
  :hints (("Goal" :expand (pseudo-termp (car assumptions))
           :in-theory (enable pseudo-termp add-refined-assumptions-to-dag-array symbol-listp))))

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

(defthm all-bounded-axe-treep-of-add-refined-assumptions-to-dag-array
  (implies (and (pseudo-term-listp assumptions)
                (all-consp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; no error:
                (not (mv-nth 0 (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)))
                (all-axe-treep acc)
                (all-bounded-axe-treep acc dag-len))
           (mv-let (erp refined-assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (add-refined-assumptions-to-dag-array assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name acc)
             (declare (ignore erp dag-array dag-parent-array dag-constant-alist dag-variable-alist))
             (all-bounded-axe-treep refined-assumptions dag-len)))
  :hints (("Goal" :expand ((pseudo-term-listp assumptions)
                           (pseudo-termp (car assumptions)))
           :in-theory (enable add-refined-assumptions-to-dag-array))))

;;;
;;; refine-assumptions-and-add-to-dag-array
;;;

;; Returns (mv erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund refine-assumptions-and-add-to-dag-array (assumptions
                                                dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                known-boolean-fns)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbol-listp known-boolean-fns))))
  (b* ((refined-terms (refine-assumptions-for-matching assumptions known-boolean-fns nil))
       ((mv erp refined-assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-refined-assumptions-to-dag-array refined-terms
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              dag-array-name
                                              dag-parent-array-name
                                              nil))
       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (refined-assumption-alist (make-refined-assumption-alist refined-assumptions)))
    (mv (erp-nil) refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm refine-assumptions-and-add-to-dag-array-return-type
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (mv-let (erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns)
             (declare (ignore erp ))
             (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (refined-assumption-alistp refined-assumption-alist)
                  (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                  (natp dag-len))))
  :hints (("Goal" :in-theory (e/d (refine-assumptions-and-add-to-dag-array) (natp)))))

(defthm refine-assumptions-and-add-to-dag-array-return-type-gen
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (mv-let (erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns)
             (declare (ignore erp DAG-ARRAY DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST))
             (implies (<= dag-len bound)
                      (bounded-refined-assumption-alistp refined-assumption-alist bound))))
  :hints (("Goal" :use (:instance refine-assumptions-and-add-to-dag-array-return-type)
           :in-theory (disable refine-assumptions-and-add-to-dag-array-return-type))))

(defthm dargp-of-mv-nth-3-of-refine-assumptions-and-add-to-dag-array-return-type
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (dargp (mv-nth 3 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
  :hints (("Goal" :use (:instance refine-assumptions-and-add-to-dag-array-return-type)
           :in-theory (disable refine-assumptions-and-add-to-dag-array-return-type))))

(defthm natp-of-mv-nth-3-of-refine-assumptions-and-add-to-dag-array-return-type
  (implies (natp dag-len)
           (natp (mv-nth 3 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable refine-assumptions-and-add-to-dag-array))))
