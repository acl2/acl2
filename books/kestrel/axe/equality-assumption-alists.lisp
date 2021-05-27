; An alist that stores equality assumptions
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

(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "equality-pairs")
(include-book "term-equal-dag")
(include-book "axe-trees")
(local (include-book "kestrel/alists-light/acons" :dir :system))

;;;
;;; term-list-to-term-alistp
;;;

;; An alist from lists of terms to single terms.
(defund term-list-to-term-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let* ((entry (first alist)))
      (and (consp entry)
           (and (pseudo-term-listp (car entry))
                (pseudo-termp (cdr entry))
                (term-list-to-term-alistp (rest alist)))))))

(defthm term-list-to-term-alistp-of-acons
  (equal (term-list-to-term-alistp (acons key val alist))
         (and (pseudo-term-listp key)
              (pseudo-termp val)
              (term-list-to-term-alistp alist)))
  :hints (("Goal" :in-theory (enable term-list-to-term-alistp))))

(defthm term-list-to-term-alistp-of-cdr
  (implies (term-list-to-term-alistp alist)
           (term-list-to-term-alistp (cdr alist)))
  :hints (("Goal" :in-theory (enable term-list-to-term-alistp))))

(defthm term-list-to-term-alistp-forward-to-alistp
  (implies (term-list-to-term-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-list-to-term-alistp))))

;move
;; Note that nil (the value returned if no match is found) is a pseudo-term.
;; (defthm pseudo-termp-of-lookup-equal-when-term-list-to-term-alistp
;;   (implies (term-list-to-term-alistp alist)
;;            (pseudo-termp (lookup-equal key alist)))
;;   :hints (("Goal" :in-theory (enable lookup-equal assoc-equal term-list-to-term-alistp))))

;; A equality-assumption-alist is a database of equality assumptions used by
;; Axe.  Conceptually, it represents a list of pairs of the form (LHS . RHS),
;; where LHS and RHS are terms and LHS is not a quoted constant and is
;; lambda-free.  The pair represents the (directed) equality of LHS and RHS.
;; For efficiency, we index the structure by the top function symbols of the
;; LHSes (using the special symbol :var for LHSes that are variables).  So the
;; structure is an alist where the keys are symbols (function symbols and
;; :var).  If the KEY of an entry is not :var, the value is an alist mapping
;; lists of terms (representing args to calls of KEY -- no need to store the
;; top function symbol in each pair) to terms (each representing a RHS).  If
;; the KEY of an entry is :var, the value is an alist mapping variables to
;; terms (each representing a RHS).

;; TODO: How can we speed this up?  Better indexing?  Add the LHSes (terms) to
;; the DAG before we start the rewrite?

(defund equality-assumption-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let* ((entry (first alist)))
      (and (consp entry)
           (let ((key (car entry))
                 (val (cdr entry)))
             (and (symbolp key) ; a function name or the special symbol :var
                  (if (eq :var key)
                      ;; Val maps vars to terms:
                      (symbol-term-alistp val)
                    ;; Normal case (function call).  Val maps lists of args
                    ;; (for calls of the function whose name is KEY) to the
                    ;; corresponding RHSes:
                    (term-list-to-term-alistp val))))
           (equality-assumption-alistp (rest alist))))))

;; (defthm equality-assumption-alistp-forward-to-alistp
;;   (implies (equality-assumption-alistp alist)
;;            (alistp alist))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable equality-assumption-alistp))))

(defthm equality-assumption-alistp-forward-to-symbol-alistp
  (implies (equality-assumption-alistp alist)
           (symbol-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable equality-assumption-alistp))))

(defthm term-list-to-term-alistp-of-lookup-equal-when-equality-assumption-alistp
  (implies (and (equality-assumption-alistp equality-assumption-alist)
                (not (equal :var fn)))
           (term-list-to-term-alistp (lookup-equal fn equality-assumption-alist)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp lookup-equal))))

(defthm alistp-of-lookup-equal-when-equality-assumption-alistp
  (implies (equality-assumption-alistp equality-assumption-alist)
           (alistp (lookup-equal fn equality-assumption-alist)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp lookup-equal))))

(defthm symbol-alistp-of-lookup-equal-of-var-when-equality-assumption-alistp
  (implies (equality-assumption-alistp equality-assumption-alist)
           (symbol-alistp (lookup-equal :var equality-assumption-alist)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp lookup-equal))))

(defthm symbol-term-alistp-of-lookup-equal-of-var-when-equality-assumption-alistp
  (implies (equality-assumption-alistp equality-assumption-alist)
           (symbol-term-alistp (lookup-equal :var equality-assumption-alist)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp lookup-equal))))

(defthm alistp-of-lookup-equal-of-var-when-equality-assumption-alistp
  (implies (equality-assumption-alistp equality-assumption-alist)
           (alistp (lookup-equal :var equality-assumption-alist)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp lookup-equal))))

;; Search ARGS-TO-RHS-ALIST for an entry whose car is a list of terms equal to
;; DARGS wrt DAG-ARRAY.  Return the cdr (the RHS) of the first such pair, or nil.
(defund replace-fun-call-using-equality-assumption-alist-aux (args-to-rhs-alist dargs dag-array)
  (declare (xargs :guard (and (term-list-to-term-alistp args-to-rhs-alist)
                              (true-listp dargs)
                              (all-dargp dargs)
                              (implies (not (all-myquotep dargs))
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep dargs)))))
                  :guard-hints (("Goal" :in-theory (enable term-list-to-term-alistp)))))
  (if (endp args-to-rhs-alist)
      nil ;failure
    (let* ((entry (first args-to-rhs-alist))
           (args-terms (car entry)))
      (if (terms-equal-dag-itemsp args-terms dargs dag-array)
          (cdr entry) ;the RHS
        (replace-fun-call-using-equality-assumption-alist-aux (rest args-to-rhs-alist) dargs dag-array)))))

;; Note that nil (the value returned if no match is found) is a pseudo-term.
(defthm pseudo-termp-of-replace-fun-call-using-equality-assumption-alist-aux
  (implies (term-list-to-term-alistp args-to-rhs-alist)
           (pseudo-termp (replace-fun-call-using-equality-assumption-alist-aux args-to-rhs-alist dargs dag-array)))
  :hints (("Goal" :in-theory (enable replace-fun-call-using-equality-assumption-alist-aux term-list-to-term-alistp))))

(defthm axe-treep-of-replace-fun-call-using-equality-assumption-alist-aux
  (implies (term-list-to-term-alistp args-to-rhs-alist)
           (axe-treep (replace-fun-call-using-equality-assumption-alist-aux args-to-rhs-alist dargs dag-array))))

;;;
;;; replace-fun-call-using-equality-assumption-alist
;;;

;; Returns a new term, or nil to indicate no change.
;; Looks up FN in the alist and searches the resulting alist for an entry of the form (lhs-args . rhs), where the LHS-ARGS are equal to ARGS and, if one is found, returns the term RHS.
(defund replace-fun-call-using-equality-assumption-alist (equality-assumption-alist fn dargs dag-array)
  (declare (xargs :guard (and (equality-assumption-alistp equality-assumption-alist)
                              (symbolp fn)
                              (not (eq 'quote fn))
                              ;; (not (eq :var fn)) ;todo: may be hard to guarantee
                              (true-listp dargs)
                              (all-dargp dargs)
                              (implies (not (all-myquotep dargs))
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep dargs)))))))
  ;; If FN is not present in the alist, the lookup-eq will give nil
  (if (eq fn :var) ;should not happen
      nil
    (replace-fun-call-using-equality-assumption-alist-aux (lookup-eq fn equality-assumption-alist) dargs dag-array)))

;; Note that nil (the value returned if no match is found) is a pseudo-term.
(defthm pseudo-termp-of-replace-fun-call-using-equality-assumption-alist
  (implies (and (equality-assumption-alistp equality-assumption-alist)
                ;;(not (equal :var fn))
                )
           (pseudo-termp (replace-fun-call-using-equality-assumption-alist equality-assumption-alist fn dargs dag-array)))
  :hints (("Goal" :in-theory (enable replace-fun-call-using-equality-assumption-alist))))

(defthm axe-treep-of-replace-fun-call-using-equality-assumption-alist
  (implies (and (equality-assumption-alistp equality-assumption-alist)
                ;;(not (equal :var fn))
                )
           (axe-treep (replace-fun-call-using-equality-assumption-alist equality-assumption-alist fn dargs dag-array)))
  :hints (("Goal" :in-theory (enable replace-fun-call-using-equality-assumption-alist))))

;;;
;;; replace-var-using-equality-assumption-alist
;;;

;; Returns a new term, or nil to indicate no change.
;; Looks up :var in the alist and then looks up var in the resulting alist, yielding a term equal to var, or nil.
(defund replace-var-using-equality-assumption-alist (equality-assumption-alist var)
  (declare (xargs :guard (and (equality-assumption-alistp equality-assumption-alist)
                              (symbolp var))))
  ;; If :var is not present in the alist, the inner lookup-eq will give nil.
  (lookup-eq var (lookup-eq :var equality-assumption-alist)))

;dup
;rename subst->alist
;; Note that nil (the value returned if no match is found) is a pseudo-term.
(defthm pseudo-termp-of-lookup-equal-when-symbol-term-alistp
  (implies (symbol-term-alistp subst)
           (pseudo-termp (lookup-equal term subst)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

;; Note that nil (the value returned if no match is found) is a pseudo-term.
(defthm pseudo-termp-of-replace-var-using-equality-assumption-alist
  (implies (equality-assumption-alistp equality-assumption-alist)
           (pseudo-termp (replace-var-using-equality-assumption-alist equality-assumption-alist var)))
  :hints (("Goal" :in-theory (enable replace-var-using-equality-assumption-alist))))

(defun pairs-to-equality-assumption-alist (term-pairs acc)
  (declare (xargs :guard (and (equality-pairsp term-pairs)
                              (equality-assumption-alistp acc))
                  :guard-hints (("Goal" :in-theory (enable equality-pairsp
                                                           equality-assumption-alistp
                                                           term-list-to-term-alistp)
                                 :expand ((all-equality-pairp term-pairs))))))
  (if (endp term-pairs)
      (uniquify-alist-eq acc) ;is this fast?
    (let* ((term-pair (first term-pairs))
           (lhs (car term-pair))
           (rhs (cdr term-pair)))
      (if (symbolp lhs)
          ;; variables are all stored under the special symbol :var
          (pairs-to-equality-assumption-alist (rest term-pairs)
                                              (acons :var (acons lhs rhs (lookup-eq :var acc)) acc))
        (let ((fn (ffn-symb lhs)))
          (if (consp fn) ; todo: handle better (should not happen - improve guard -- or expand lambdas):
              (er hard? 'pairs-to-equality-assumption-alist "Detected a lambda.")
            (if (eq 'quote fn) ; todo: handle better (should not happen - improve guard -- but this does happen in some lifter examples):
                (prog2$ (cw "WARNING: Detected a quotep LHS in equality assumption pair ~X01.~%" term-pair nil)
                        ;; skip it:
                        (pairs-to-equality-assumption-alist (rest term-pairs) acc))
              (if (eq ':var fn) ; todo: handle better (should not happen - improve guard):
                  (er hard? 'pairs-to-equality-assumption-alist "Detected a call to :var.")
                ;; bind the lhs-args to the rhs:
                (pairs-to-equality-assumption-alist (rest term-pairs)
                                                    (acons fn (acons (fargs lhs) rhs (lookup-eq fn acc)) acc))))))))))

(defthm equality-assumption-alistp-of-uniquify-alist-eq-aux
  (implies (and (equality-assumption-alistp alist)
                (equality-assumption-alistp acc))
           (equality-assumption-alistp (uniquify-alist-eq-aux alist acc)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp uniquify-alist-eq-aux))))

(defthm equality-assumption-alistp-of-uniquify-alist-eq
  (implies (and (equality-assumption-alistp alist)
                (equality-assumption-alistp acc))
           (equality-assumption-alistp (uniquify-alist-eq alist)))
  :hints (("Goal" :in-theory (enable uniquify-alist-eq))))

(defthm equality-assumption-alistp-of-pairs-to-equality-assumption-alist
  (implies (and (equality-pairsp term-pairs)
                (equality-assumption-alistp acc))
           (equality-assumption-alistp (pairs-to-equality-assumption-alist term-pairs acc)))
  :hints (("Goal" :in-theory (enable equality-assumption-alistp equality-pairsp))))

;ASSUMPTIONS is a list of terms
;returns a list of dotted pairs of terms
(defun make-equality-assumption-alist (assumptions wrld)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (plist-worldp wrld))))
  (let ((term-pairs (add-equality-pairs-for-assumptions assumptions (known-booleans wrld) nil)))
    (pairs-to-equality-assumption-alist term-pairs nil)))

;; (make-equality-assumption-alist '((equal (foo x) (bar x '3 y)) (equal (foo y) (bar x '3 z)) (equal w (vaz x '3)) (equal w2 (baz x '3))) (w state))

(defthm equality-assumption-alistp-of-equality-assumption-alist
  (implies (pseudo-term-listp assumptions)
           (equality-assumption-alistp (make-equality-assumption-alist assumptions wrld))))
