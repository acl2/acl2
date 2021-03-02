; Matching a term with part of a DAG
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

;; This book deals with one-way matching pseudo-terms with (parts of) dag-arrays.
;; See also unify-term-and-dag-fast.lisp for an optimized version.

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "dag-arrays")
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(mutual-recursion

 ;; Term is a pseudo-term, not an axe-tree (e.g., it comes from the lhs of a rule).
 ;; Returns :fail or an alist giving values to all the variables in the term (TODO: Prove that)
 ;; The ALIST returned (and ALIST-ACC) binds variables from the term to nodenums and/or quoteps.
 ;; Any time a variable in the term gets unified, it must match the binding already present (if any) for that variable in ALIST-ACC.
 ;; A term containing lambdas won't match, since lambdas are not present in DAGs, but that won't matter if TERM is the LHS of an axe-rule (which must be lambda-free).
 ;; It would be convenient to use nil to indicate failure (would allow ANDing the two recursive calls), but nil may just mean that the subtree in question has no vars, so we use :fail.
 ;; TODO: Make a version of this that just checks the vars, and call it once we know the skeleton of function calls and constants matches.
 ;; TODO: possible optimization: instead of consing up an alist, transform the vars into array indices and fill in the appropriate slots?
 ;; TODO: Compare to unify-term-and-dag-item.
 (defund unify-term-and-dag (term darg dag-array dag-len alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (dargp-less-than darg dag-len)
                               (symbol-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (consp term)
       ;; Term is a cons, so it's either a function call or a quoted constant:
       (let ((fn (ffn-symb term)))
         (if (eq 'quote fn)
             ;; Term is a quoted constant (the only thing that matches is that constant -- we are now inlining all constants)
             (if (and (consp darg) ;if it's a consp it must be a quotep (nodenums are integers)
                      (equal (unquote term) (unquote darg)))
                 alist
               :fail)
           ;; Term is a regular function call (the only thing that matches is a call to the same function with args that match)
           (if (consp darg) ;tests whether it's a quotep
               :fail ;can't unify a term that's a function call with an item that's a quoted constant (could add fancy support for this like acl2 has...)
             ;; The darg is a nodenum:
             (let ((item-expr (aref1 'dag-array dag-array darg)))
               (if (call-of fn item-expr)
                   (unify-terms-and-dag (fargs term) (dargs item-expr) dag-array dag-len alist)
                 :fail)))))
     ;; Term is not a consp, so it must be a variable:
     (let ((previous-binding (assoc-eq term alist)))
       (if previous-binding
           ;; If there's a previous binding for the variable, it must match the current item:
           ;; (what if it was bound to a quotep and now we have the nodenum of the quotep - better to always inline?)
           (if (equal (cdr previous-binding) darg)
               alist
             :fail)
         ;; If there was no previous binding, make one now..
         (acons-fast term darg alist)))))

 ;; Returns :fail or an alist giving values to all the variables in the term (TODO: Prove that)
 (defund unify-terms-and-dag (terms dargs dag-array dag-len alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (true-listp dargs)
                               (all-dargp-less-than dargs dag-len)
                               (symbol-alistp alist)
                               ;; (same-lengthp terms dargs) ;; should be true, but we don't want the caller to have to ensure this
                               )
                   :verify-guards nil ;done below
                   ))
   (if (endp terms)
       ;; everything matched, so return the alist:
       alist
     (if (consp dargs) ;for guards, could drop if we knew that all arities were consistent
         (let ((alist-or-fail (unify-term-and-dag (first terms) (first dargs) dag-array dag-len alist)))
           (if (eq :fail alist-or-fail)
               :fail
             (unify-terms-and-dag (rest terms) (rest dargs) dag-array dag-len alist-or-fail)))
       (prog2$ (er hard? 'unify-terms-and-dag "Arity mismatch.")
               :fail)))))

(make-flag unify-term-and-dag)

(defthm-flag-unify-term-and-dag
  (defthm symbol-alistp-of-unify-term-and-dag
    (implies (and (symbol-alistp alist)
                  (pseudo-termp term)
                  (not (equal :fail (unify-term-and-dag term darg dag-array dag-len alist))))
             (symbol-alistp (unify-term-and-dag term darg dag-array dag-len alist)))
    :flag unify-term-and-dag)
  (defthm symbol-alistp-of-unify-terms-and-dag
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp terms)
                  (not (equal :fail (unify-terms-and-dag terms dargs dag-array dag-len alist))))
             (symbol-alistp (unify-terms-and-dag terms dargs dag-array dag-len alist)))
    :flag unify-terms-and-dag)
  :hints (("Goal" :expand ((unify-terms-and-dag terms dargs dag-array dag-len alist)
                           (unify-terms-and-dag nil dargs dag-array dag-len alist)
                           (unify-term-and-dag term darg dag-array dag-len alist)
                           (unify-term-and-dag term (cdr (assoc-equal term alist)) dag-array dag-len alist)))))

(verify-guards unify-term-and-dag)

(defthm-flag-unify-term-and-dag
  (defthm alistp-of-unify-term-and-dag
    (implies (and (alistp alist)
                  ;;(pseudo-termp term)
                  (not (equal :fail (unify-term-and-dag term darg dag-array dag-len alist))))
             (alistp (unify-term-and-dag term darg dag-array dag-len alist)))
    :flag unify-term-and-dag)
  (defthm alistp-of-unify-terms-and-dag
    (implies (and (alistp alist)
                  ;;(pseudo-term-listp terms)
                  (not (equal :fail (unify-terms-and-dag terms dargs dag-array dag-len alist))))
             (alistp (unify-terms-and-dag terms dargs dag-array dag-len alist)))
    :flag unify-terms-and-dag)
  :hints (("Goal" :expand ((unify-terms-and-dag terms dargs dag-array dag-len alist)
                           (unify-terms-and-dag nil dargs dag-array dag-len alist)
                           (unify-term-and-dag term darg dag-array dag-len alist)
                           (unify-term-and-dag term (cdr (assoc-equal term alist)) dag-array dag-len alist)))))

(defthm-flag-unify-term-and-dag
  (defthm all-dargp-of-strip-cdrs-of-unify-term-and-dag
    (implies (and (all-dargp (strip-cdrs alist))
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-termp term)
                  (natp darg)
                  (< darg dag-len)
                  (not (equal :fail (unify-term-and-dag term darg dag-array dag-len alist))))
             (all-dargp (strip-cdrs (unify-term-and-dag term darg dag-array dag-len alist))))
    :flag unify-term-and-dag)
  (defthm all-dargp-of-strip-cdrs-of-unify-terms-and-dag
    (implies (and (all-dargp (strip-cdrs alist))
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-term-listp terms)
                  (all-dargp-less-than dargs dag-len)
                  ;(equal (len dargs) (len terms))
                  (not (equal :fail (unify-terms-and-dag terms dargs dag-array dag-len alist))))
             (all-dargp (strip-cdrs (unify-terms-and-dag terms dargs dag-array dag-len alist))))
    :flag unify-terms-and-dag)
  :hints (("Goal" :in-theory (enable INTEGERP-OF-CAR-WHEN-ALL-DARGP)
           :expand ((UNIFY-TERM-AND-DAG (CAR TERMS)
                                        (CAR DARGS)
                                        DAG-ARRAY DAG-LEN ALIST)
                    (unify-terms-and-dag terms dargs dag-array dag-len alist)
                    (unify-terms-and-dag nil dargs dag-array dag-len alist)
                    (unify-term-and-dag term darg dag-array dag-len alist)
                    (unify-term-and-dag term (cdr (assoc-equal term alist)) dag-array dag-len alist)))))

(defthm-flag-unify-term-and-dag
  (defthm all-dargp-less-than-of-strip-cdrs-of-unify-term-and-dag
    (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-termp term)
                  (natp darg)
                  (< darg dag-len)
                  (not (equal :fail (unify-term-and-dag term darg dag-array dag-len alist))))
             (all-dargp-less-than (strip-cdrs (unify-term-and-dag term darg dag-array dag-len alist))
                                             dag-len))
    :flag unify-term-and-dag)
  (defthm all-dargp-less-than-of-strip-cdrs-of-unify-terms-and-dag
    (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-term-listp terms)
                  (all-dargp-less-than dargs dag-len)
                  ;(equal (len dargs) (len terms))
                  (not (equal :fail (unify-terms-and-dag terms dargs dag-array dag-len alist))))
             (all-dargp-less-than (strip-cdrs (unify-terms-and-dag terms dargs dag-array dag-len alist))
                                              dag-len))
    :flag unify-terms-and-dag)
  :hints (("Goal" :in-theory (enable INTEGERP-OF-CAR-WHEN-ALL-DARGP)
           :expand ((UNIFY-TERM-AND-DAG (CAR TERMS)
                                        (CAR DARGS)
                                        DAG-ARRAY DAG-LEN ALIST)
                    (unify-terms-and-dag terms dargs dag-array dag-len alist)
                    (unify-terms-and-dag nil dargs dag-array dag-len alist)
                    (unify-term-and-dag term darg dag-array dag-len alist)
                    (unify-term-and-dag term (cdr (assoc-equal term alist)) dag-array dag-len alist)))))
