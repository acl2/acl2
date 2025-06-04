; An alist that stores assumptions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "renaming-array")
(include-book "axe-trees")
(include-book "refine-assumptions")
(include-book "darg-listp")
;(include-book "kestrel/utilities/forms" :dir :system)
;(include-book "kestrel/utilities/erp" :dir :system)
;(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;; Usage (see refine-assumptions-and-add-to-dag-array):
;;;
;;; 1. Call refine-assumptions-for-matching to produce a list of terms.
;;;
;;; 2. Call add-refined-assumptions-to-dag-array to add the args of the refined
;;;    assumptions to the dag-array, yielding a list of function call exprs.
;;;
;;; 3. Call make-refined-assumption-alist on the resulting exprs.

;; See also the comment "How we use the refined-assumption-alist" in make-rewriter-simple.lisp

;; See also refined-assumption-alists2.lisp
;; See also refined-assumption-alists3.lisp

(local (in-theory (disable symbol-listp ; prevent inductions
                           wf-dagp wf-dagp-expander)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A "refined-assumption-alist" is an efficient way to store a list of
;; axe-trees, each of which is a function call applied to a darg-list (args that are nodenums
;; / quoteps).  We use "term indexing": the alist maps each topmost function, FN, to
;; a list of darg-lists (one for each call of FN).
;; TODO: Consider using a property list world or fast alist instead of an alist.

(defun darg-list-listp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (darg-listp (first items))
         (darg-list-listp (rest items)))))

(defun refined-assumption-alist-entryp (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       (symbolp (car entry)) ;; should lambdas be allowed?
       ;; (not (eq 'quote (car entry))) ;; TODO: Uncomment
       (darg-list-listp (cdr entry)) ; checks that each member of (cdr entry) is a list of nodenum/quoteps
       ))

;could add more checks to this
(defund refined-assumption-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (and (refined-assumption-alist-entryp (first alist))
         (refined-assumption-alistp (rest alist)))))

(local
  (defthm refined-assumption-alistp-forward-to-alistp
    (implies (refined-assumption-alistp alist)
             (alistp alist))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable refined-assumption-alistp)))))

;disable?
(defthm symbol-alistp-when-refined-assumption-alistp-cheap
  (implies (refined-assumption-alistp acc)
           (symbol-alistp acc))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable refined-assumption-alistp))))

;; todo: ensure we always use lookup-in-refined-assumption-alist and then remove these
(local
  (defthm true-listp-of-lookup-equal-when-refined-assumption-alistp-cheap
    (implies (refined-assumption-alistp alist)
             (true-listp (lookup-equal sym alist)))
    :rule-classes ((:rewrite :backchain-limit-lst (0)))
    :hints (("Goal" :in-theory (enable refined-assumption-alistp)))))

(local
  (defthm darg-list-listp-of-lookup-equal-when-refined-assumption-alistp
    (implies (refined-assumption-alistp alist)
             (darg-list-listp (lookup-equal fn alist)))
    :hints (("Goal" :in-theory (enable refined-assumption-alistp)))))

(local
  (defthm refined-assumption-alistp-of-cons
    (equal (refined-assumption-alistp (cons entry alist))
           (and ;; or call (refined-assumption-alist-entryp entry)
                (consp entry)
                (symbolp (car entry))
                (darg-list-listp (cdr entry))
                (refined-assumption-alistp alist)))
    :hints (("Goal" :in-theory (enable refined-assumption-alistp)))))

(local
  (defthm refined-assumption-alistp-of-uniquify-alist-eq-aux
    (implies (and (refined-assumption-alistp acc)
                  (refined-assumption-alistp alist))
             (refined-assumption-alistp (uniquify-alist-eq-aux alist acc)))
    :hints (("Goal" :in-theory (enable refined-assumption-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Looks up a function in the refined-assumption-alist.
;; Returns a list of lists of dargs
;; This is just lookup-eq (currently) but is kept separate to make a nice
;; abstraction for refined-assumption-alists (and note the guard).
(defund-inline lookup-in-refined-assumption-alist (fn refined-assumption-alist)
  (declare (xargs :guard (and (symbolp fn)
                              (refined-assumption-alistp refined-assumption-alist))))
  (lookup-eq fn refined-assumption-alist))

(defthm darg-list-listp-of-lookup-in-refined-assumption-alist
  (implies (refined-assumption-alistp refined-assumption-alist)
           (darg-list-listp (lookup-in-refined-assumption-alist fn refined-assumption-alist)))
  :hints (("Goal" :in-theory (enable lookup-in-refined-assumption-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; bounded refined-assumption-alists
;;;

;; Recognizes a true-list of bounded darg lists.
(defund bounded-darg-list-listp (items dag-len)
  (declare (xargs :guard (natp dag-len)))
  (if (atom items)
      (null items)
    (and (bounded-darg-listp (first items) dag-len)
         (bounded-darg-list-listp (rest items) dag-len))))

(defthm bounded-darg-list-listp-forward-to-true-listp
  (implies (bounded-darg-list-listp items dag-len)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-of-nil
  (bounded-darg-list-listp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-of-cons
  (equal (bounded-darg-list-listp (cons a x) dag-len)
         (and (bounded-darg-listp a dag-len)
              (bounded-darg-list-listp x dag-len)))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-monotone
  (implies (and (bounded-darg-list-listp alist bound2)
                (<= bound2 bound))
           (bounded-darg-list-listp alist bound))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-listp-of-car
  (implies (bounded-darg-list-listp items dag-len)
           (bounded-darg-listp (car items) dag-len))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-of-cdr
  (implies (bounded-darg-list-listp items dag-len)
           (bounded-darg-list-listp (cdr items) dag-len))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm darg-list-listp-when-bounded-darg-list-listp
  (implies (bounded-darg-list-listp items bound)
           (darg-list-listp items))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthmd true-list-of-car-when-bounded-darg-list-listp
  (implies (and (bounded-darg-list-listp assumption-arg-lists dag-len)
                (consp assumption-arg-lists))
           (true-listp (car assumption-arg-lists))))

(defthmd darg-listp-of-car-when-bounded-darg-list-listp
  (implies (and (bounded-darg-list-listp assumption-arg-lists dag-len)
                (consp assumption-arg-lists))
           (darg-listp (car assumption-arg-lists))))

;;;
;;; bounded-refined-assumption-alistp
;;;

(defund bounded-refined-assumption-alistp (alist bound)
  (declare (xargs :guard (natp bound)))
  (if (atom alist)
      (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symbolp (car entry)) ;; should lambdas be allowed?
           ;; (not (eq 'quote (car entry))) ;; TODO: Uncomment
           (bounded-darg-list-listp (cdr entry) bound)
           (bounded-refined-assumption-alistp (cdr alist) bound)))))

(defthm refined-assumption-alistp-when-bounded-refined-assumption-alistp
  (implies (bounded-refined-assumption-alistp alist bound)
           (refined-assumption-alistp alist))
  :hints (("Goal" :in-theory (e/d (bounded-refined-assumption-alistp refined-assumption-alistp)
                                  (darg-list-listp)))))

(local
  (defthm bounded-darg-list-listp-of-lookup-equal-when-bounded-refined-assumption-alistp
    (implies (bounded-refined-assumption-alistp refined-assumption-alist bound)
             (bounded-darg-list-listp (lookup-equal fn refined-assumption-alist) bound))
    :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp lookup-equal assoc-equal)))))

(defthm bounded-darg-list-listp-of-lookup-in-refined-assumption-alist
  (implies (bounded-refined-assumption-alistp refined-assumption-alist bound)
           (bounded-darg-list-listp (lookup-in-refined-assumption-alist fn refined-assumption-alist) bound))
  :hints (("Goal" :in-theory (enable lookup-in-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-monotone
  (implies (and (bounded-refined-assumption-alistp alist bound2)
                (<= bound2 bound))
           (bounded-refined-assumption-alistp alist bound))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp))))

(local
  (defthm bounded-refined-assumption-alistp-of-uniquify-alist-eq-aux
    (implies (and (bounded-refined-assumption-alistp alist bound)
                  (bounded-refined-assumption-alistp acc bound))
             (bounded-refined-assumption-alistp (uniquify-alist-eq-aux alist acc) bound))
    :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp uniquify-alist-eq-aux)))))

(defthm bounded-refined-assumption-alistp-forward-to-symbol-alistp
  (implies (bounded-refined-assumption-alistp refined-assumption-alist bound)
           (symbol-alistp refined-assumption-alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adds the EXPRS to the REFINED-ASSUMPTION-ALIST.
;the exprs are fn calls applied to dargs (nodenums / quoteps)
;; We could optimize this using fast alists or property list worlds.
(defund extend-refined-assumption-alist (exprs refined-assumption-alist)
  (declare (xargs :guard (and (true-listp exprs)
                              (all-dag-function-call-exprp exprs)
                              (refined-assumption-alistp refined-assumption-alist))))
  (if (endp exprs)
      (uniquify-alist-eq refined-assumption-alist)
    (b* ((expr (first exprs))
         (fn (ffn-symb expr))
         (args (dargs expr))
         (arg-lists-for-fn (lookup-eq fn refined-assumption-alist))
         (new-arg-lists-for-fn (cons args arg-lists-for-fn)))
        (extend-refined-assumption-alist (rest exprs)
                                         (acons-fast fn new-arg-lists-for-fn refined-assumption-alist)))))

(defthm refined-assumption-alistp-of-extend-refined-assumption-alist
  (implies (and (refined-assumption-alistp refined-assumption-alist)
                (all-dag-function-call-exprp exprs))
           (refined-assumption-alistp (extend-refined-assumption-alist exprs refined-assumption-alist)))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist
  (implies (and (bounded-refined-assumption-alistp refined-assumption-alist bound)
                (all-dag-function-call-exprp exprs)
                (bounded-dag-expr-listp bound exprs))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist exprs refined-assumption-alist) bound))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp extend-refined-assumption-alist
                                     dag-function-call-exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a refined-assumption-alist representing the EXPRS.
(defund make-refined-assumption-alist (exprs)
  (declare (xargs :guard (and (true-listp exprs)
                              (all-dag-function-call-exprp exprs))))
  (extend-refined-assumption-alist exprs nil))

(defthm refined-assumption-alistp-of-make-refined-assumption-alist
  (implies (all-dag-function-call-exprp exprs)
           (refined-assumption-alistp (make-refined-assumption-alist exprs)))
  :hints (("Goal" :in-theory (enable make-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-of-make-refined-assumption-alist
  (implies (and (all-dag-function-call-exprp exprs)
                (bounded-dag-expr-listp bound exprs))
           (bounded-refined-assumption-alistp (make-refined-assumption-alist exprs) bound))
  :hints (("Goal" :in-theory (enable make-refined-assumption-alist
                                     bounded-refined-assumption-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; First, refine the assumptions for matching.  Then, add each one's args to the DAG.  Finally, build the refined-assumption-alist.
;; could move this to a different book.
(defund refine-assumptions-and-add-to-dag-array (assumptions
                                                 dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                 known-boolean-fns)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbol-listp known-boolean-fns))))
  (b* ((refined-terms (refine-assumptions-for-matching assumptions known-boolean-fns nil))
       ((mv erp refined-assumption-exprs dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-refined-assumptions-to-dag-array refined-terms
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              dag-array-name
                                              dag-parent-array-name
                                              nil))
       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (refined-assumption-alist (make-refined-assumption-alist refined-assumption-exprs)))
    (mv (erp-nil) refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm refine-assumptions-and-add-to-dag-array-return-type
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (mv-let (erp refined-assumption-alist dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns)
             (declare (ignore erp ))
             (and (wf-dagp dag-array-name dag-array new-dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (refined-assumption-alistp refined-assumption-alist)
                  (bounded-refined-assumption-alistp refined-assumption-alist new-dag-len)
                  (natp new-dag-len)
                  (<= dag-len new-dag-len))))
  :hints (("Goal" :in-theory (e/d (refine-assumptions-and-add-to-dag-array) (natp)))))

(defthm refine-assumptions-and-add-to-dag-array-return-type-gen
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (mv-let (erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns)
             (declare (ignore erp dag-array dag-parent-array dag-constant-alist dag-variable-alist))
             (implies (<= dag-len bound)
                      (bounded-refined-assumption-alistp refined-assumption-alist bound))))
  :hints (("Goal" :use (:instance refine-assumptions-and-add-to-dag-array-return-type)
           :in-theory (disable refine-assumptions-and-add-to-dag-array-return-type))))

(defthm natp-of-mv-nth-3-of-refine-assumptions-and-add-to-dag-array-return-type
  (implies (natp dag-len)
           (natp (mv-nth 3 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable refine-assumptions-and-add-to-dag-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund append-nodenum-dargs-list (darg-lists acc)
  (declare (xargs :guard (and (darg-list-listp darg-lists)
                              (nat-listp acc))))
  (if (endp darg-lists)
      acc
    (append-nodenum-dargs-list (rest darg-lists) (append-nodenum-dargs (first darg-lists) acc))))

(local
  (defthm true-listp-of-append-nodenum-dargs-list-type
    (implies (true-listp acc)
             (true-listp (append-nodenum-dargs-list darg-lists acc)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable append-nodenum-dargs-list)))))

(local
  (defthm nat-listp-of-append-nodenum-dargs-list
    (implies (darg-list-listp darg-lists)
             (equal (nat-listp (append-nodenum-dargs-list darg-lists acc))
                    (nat-listp acc)))
    :hints (("Goal" :in-theory (enable append-nodenum-dargs-list)))))

(local
  (defthm all-<-of-append-nodenum-dargs-list
    (implies (and (bounded-darg-list-listp darg-lists bound)
                  (all-< acc bound))
             (all-< (append-nodenum-dargs-list darg-lists acc) bound))
    :hints (("Goal" :in-theory (enable append-nodenum-dargs-list
                                       bounded-darg-list-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For extracting relevant nodes, for printing.
(defund nodenums-in-refined-assumption-alist (alist acc)
  (declare (xargs :guard (and (refined-assumption-alistp alist)
                              (nat-listp acc))))
  (if (endp alist)
      acc
    (let ((entry (car alist)))
      (nodenums-in-refined-assumption-alist (rest alist)
                                            (append-nodenum-dargs-list (cdr entry) acc)))))

(defthm nat-listp-of-nodenums-in-refined-assumption-alist-type
  (implies (and (refined-assumption-alistp alist)
                (nat-listp acc))
           (nat-listp (nodenums-in-refined-assumption-alist alist acc)))
  :hints (("Goal" :in-theory (enable nodenums-in-refined-assumption-alist))))

(defthm true-listp-of-nodenums-in-refined-assumption-alist-type
  (implies (true-listp acc)
           (true-listp (nodenums-in-refined-assumption-alist alist acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable nodenums-in-refined-assumption-alist))))

(defthm all-<-of-nodenums-in-refined-assumption-alist
  (implies (and (bounded-refined-assumption-alistp alist bound)
                (all-< acc bound))
           (all-< (nodenums-in-refined-assumption-alist alist acc) bound))
  :hints (("Goal" :in-theory (enable nodenums-in-refined-assumption-alist all-< bounded-refined-assumption-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun print-fn-applications-on-darg-lists (fn darg-lists fns-to-elide firstp)
  (declare (xargs :guard (and (symbolp fn)
                              (darg-list-listp darg-lists)
                              (symbol-listp fns-to-elide)
                              (booleanp firstp))))
  (if (endp darg-lists)
      nil
    (let ((darg-list (first darg-lists)))
      (prog2$ (if (member-eq fn fns-to-elide)
                  ;; todo: only elide if some darg in darg-list is a large constant
                  (if firstp
                      (cw "((~x0 ...)~%" fn)
                    (cw " (~x0 ...)~%" fn))
                (if firstp
                    (cw "(~y0" (cons fn darg-list))
                  (cw " ~y0" (cons fn darg-list))))
              (print-fn-applications-on-darg-lists fn (rest darg-lists) fns-to-elide nil)))))

;; (defun print-refined-assumption-alist-entry-elided (entry fns-to-elide firstp)
;;   (declare (xargs :guard (and (refined-assumption-alist-entryp entry)
;;                               (symbol-listp fns-to-elide)
;;                               (booleanp firstp))))
;;   (let ((fn (car entry)))
;;     (if (member-eq fn fns-to-elide)
;;         (cw "(~x0 ...)~%" fn)
;;       (print-fn-applications-on-darg-lists fn (cdr entry) firstp))))

(defund print-refined-assumption-alist-elided-aux (alist fns-to-elide firstp)
  (declare (xargs :guard (and (refined-assumption-alistp alist)
                              (symbol-listp fns-to-elide)
                              (booleanp firstp))
                  :guard-hints (("Goal" :in-theory (enable refined-assumption-alistp)))))
  (if (atom alist)
      (cw ")") ; balances the paren printed for the first item
    (let ((entry (first alist)))
      (prog2$ (print-fn-applications-on-darg-lists (car entry) (cdr entry) fns-to-elide firstp)
              (print-refined-assumption-alist-elided-aux (rest alist) fns-to-elide nil)))))

(defund print-refined-assumption-alist-elided (alist fns-to-elide)
  (declare (xargs :guard (and (refined-assumption-alistp alist)
                              (symbol-listp fns-to-elide))))
  (if (consp alist)
      (print-refined-assumption-alist-elided-aux alist fns-to-elide t)
    (cw "nil") ; or could print "()"
    ))
