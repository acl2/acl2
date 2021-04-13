; A faster version of the code in unify-term-and-dag.lisp.
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

;; See unify-term-and-dag-fast-correct.lisp for a proof of correctness of this code.


;; Before attempting the full (one-way) unification (which involves building an
;; alist), this quickly checks whether the term is of the right shape (ex: "foo
;; of bar of baz of 255").  Most tries will probably fail at that stage,
;; especially in a large rule-set.

;; TODO: Consider marking rules for which the pre-filter will never fail (e.g.,
;; ones of the form (foo <var> <var>), and avoid the prefilter for them.

;; TODO: Consider marking variables that occur only once in the rule and don't
;; bother binding them in the alist.

;; TODO: Consider marking each occurence of a var in the lhs according to
;; whether it is the first occurence of that var (don't bother to look it up in
;; the alist) or a later occurrence (check the alist but don't consider binding
;; the var because it is bound).

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "dag-arrays")
(local (include-book "kestrel/alists-light/alistp" :dir :system))

;;;
;;; term-skeleton-matches-dagp
;;;

(mutual-recursion
 ;; Tests whether the item matches the pattern in terms of function call structure and quoted constants - does not check that a repeated var matches the same thing both times and does not build an alist!
 ;; This should be much cheaper on calls that will fail than the version that does build an alist (and most calls should fail).
 (defund term-skeleton-matches-dagp (term darg dag-array)
   (declare (xargs :guard (and (pseudo-termp term)
                               (dargp darg)
                               (if (natp darg)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))
                                 t))))
   (if (consp term)
       ;; Term is a cons, so it's either a function call or a quoted constant:
       (let ((pat-fn (ffn-symb term)))
         (if (eq 'quote pat-fn)
             ;; Term is a quoted constant (the only thing that matches is that constant -- we are now inlining all constants)
             (and (consp darg) ;if it's a consp it must be a quotep (nodenums are integers)
                  (equal (unquote term) (unquote darg)))
           ;; Term is a regular function call (the only thing that matches is a call to the same function with args that match)
           (if (consp darg) ;tests whether it's a quotep
               nil ;can't unify a term that's a function call with an item that's a quoted constant (could add fancy support for this like acl2 has...)
             ;; The darg is a nodenum:
             (let ((darg-expr (aref1 'dag-array dag-array darg)))
               (and (call-of pat-fn darg-expr)
                    (term-skeletons-match-dagp (fargs term) (dargs darg-expr) dag-array))))))
     ;; Term is not a consp, so it must be a variable (this function always succeeds on variables - they will be checked later):
     t))

 (defund term-skeletons-match-dagp (terms dargs dag-array)
   (declare (xargs :guard (and (and (pseudo-term-listp terms)
                                    (all-dargp dargs)
                                    (true-listp dargs)
                                    (true-listp terms)
                                    (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep dargs)))
                                    ;; (same-lengthp terms dargs) ;; should be true, but we don't want the caller to have to ensure this
                                    ))))
   (if (endp terms)
       ;;everything matched:
       t
     (and (consp dargs) ;for guards, could drop if we knew that all arities were consistent
          (term-skeleton-matches-dagp (first terms) (first dargs) dag-array)
          (term-skeletons-match-dagp (rest terms) (rest dargs) dag-array)))))

(mutual-recursion

 ;; Term is a pseudo-term, not an axe-tree (e.g., it comes from the lhs of a rule).
 ;; Returns :fail or an alist giving values to all the variables in the term.
 ;; The ALIST returned (and ALIST-ACC) binds variables from the term to nodenums and/or quoteps.
 ;; Any time a variable in the term gets unified, it must match the binding already present (if any) for that variable in ALIST-ACC.
 ;; A term containing lambdas won't match, since lambdas are not present in DAGs, but LHSes of rules are lambda-free.
 ;; It would be convenient to use nil to indicate failure (would allow ANDin the two recursive calls), but nil may just mean that the subtree in question has no vars, so we use :fail.
 ;; TODO: Don't pass through dag-len
 (defund unify-term-and-dag-when-skeleton-correct (term darg dag-array dag-len alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (dargp-less-than darg dag-len)
                               (term-skeleton-matches-dagp term darg dag-array)
                               (symbol-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (consp term)
       ;; Term is a cons, so it's either a function call or a quoted constant:
       (if (eq 'quote (ffn-symb term))
           ;; Term is a constant, and we know the skeletons match:
           alist
         ;; Term is a function call.  We know darg is a nodenum whose expr is a call of the same function, since the skeletons match.  So we just have to check the args:
         (let ((darg-expr (aref1 'dag-array dag-array (the (integer 0 *) darg)))) ;todo: strengthen type decl? or drop it?
           (unify-terms-and-dag-when-skeleton-correct (fargs term) (dargs (the cons darg-expr)) dag-array dag-len alist)))
     ;; Term is not a cons, so it must be a variable:
     (let ((previous-binding (assoc-eq (the symbol term) alist)))
       (if previous-binding
           ;; If there's a previous binding for the variable, it must match the current item:
           ;;(what if it was bound to a quotep and now we have the nodenum of the quotep - better to always inline?)
           (if (equal (cdr previous-binding) darg)
               alist
             :fail)
         ;; If there was no previous binding, make one now:
         (acons-fast term darg alist)))))

 (defund unify-terms-and-dag-when-skeleton-correct (terms dargs dag-array dag-len alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (true-listp dargs)
                               (all-dargp-less-than dargs dag-len)
                               (term-skeletons-match-dagp terms dargs dag-array)
                               (symbol-alistp alist)
                               ;; (same-lengthp terms dargs) ;; should be true, but we don't want the caller to have to ensure this
                               )))
   (if (endp terms)
       ;;everything matched, so return the alist
       alist
     ;; We know (consp dargs) since the skeletons match
     (let ((alist-or-fail (unify-term-and-dag-when-skeleton-correct (first terms) (first (the cons dargs)) dag-array dag-len alist)))
       (if (eq :fail alist-or-fail)
           :fail
         (unify-terms-and-dag-when-skeleton-correct (rest terms) (rest (the cons dargs)) dag-array dag-len alist-or-fail))))))

(make-flag unify-term-and-dag-when-skeleton-correct)

(defthm-flag-unify-term-and-dag-when-skeleton-correct
  (defthm symbol-alistp-of-unify-term-and-dag-when-skeleton-correct
    (implies (and (symbol-alistp alist)
                  (pseudo-termp term)
                  (not (equal :fail (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist))))
             (symbol-alistp (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)))
    :flag unify-term-and-dag-when-skeleton-correct)
  (defthm symbol-alistp-of-unify-terms-and-dag-when-skeleton-correct
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp terms)
                  (not (equal :fail (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist))))
             (symbol-alistp (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)))
    :flag unify-terms-and-dag-when-skeleton-correct)
  :hints (("Goal" :expand ((unify-term-and-dag-when-skeleton-correct
                            term darg dag-array dag-len alist)
                           (unify-term-and-dag-when-skeleton-correct
                            term (cdr (assoc-equal term alist))
                            dag-array dag-len alist))
           :in-theory (enable unify-terms-and-dag-when-skeleton-correct))))

(verify-guards unify-term-and-dag-when-skeleton-correct
  :hints (("Goal" :in-theory (enable term-skeletons-match-dagp
                                     dargp-less-than
                                     term-skeleton-matches-dagp))))

(defthm-flag-unify-term-and-dag-when-skeleton-correct
  (defthm alistp-of-unify-term-and-dag-when-skeleton-correct
    (implies (and (alistp alist)
                  ;(pseudo-termp term)
                  (not (equal :fail (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist))))
             (alistp (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)))
    :flag unify-term-and-dag-when-skeleton-correct)
  (defthm alistp-of-unify-terms-and-dag-when-skeleton-correct
    (implies (and (alistp alist)
                  ;(pseudo-term-listp terms)
                  (not (equal :fail (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist))))
             (alistp (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)))
    :flag unify-terms-and-dag-when-skeleton-correct)
  :hints (("Goal" :in-theory (enable unify-terms-and-dag-when-skeleton-correct
                                     unify-term-and-dag-when-skeleton-correct))))

(defthm consp-of-unify-term-and-dag-when-skeleton-correct
  (implies (and (alistp alist)
                ;;(pseudo-termp term)
                (not (equal :fail (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)))
                (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist))
           (consp (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:instance alistp-of-unify-term-and-dag-when-skeleton-correct)
           :in-theory (disable alistp-of-unify-term-and-dag-when-skeleton-correct))))

(defthm true-listp-of-unify-terms-and-dag-when-skeleton-correct
  (implies (and (alistp alist)
                ;;(pseudo-term-listp terms)
                (not (equal :fail (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)))
                (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist))
           (consp (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:instance alistp-of-unify-terms-and-dag-when-skeleton-correct)
           :in-theory (disable alistp-of-unify-terms-and-dag-when-skeleton-correct))))

(defthm-flag-unify-term-and-dag-when-skeleton-correct
  (defthm all-dargp-less-than-of-strip-cdrs-of-unify-term-and-dag-when-skeleton-correct
    (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-termp term)
                  (dargp-less-than darg dag-len)
                  (not (equal :fail (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)))
                  (term-skeleton-matches-dagp term darg dag-array))
             (all-dargp-less-than (strip-cdrs (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)) dag-len))
    :flag unify-term-and-dag-when-skeleton-correct)
  (defthm all-dargp-less-than-of-strip-cdrs-of-unify-terms-and-dag-when-skeleton-correct
    (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-term-listp terms)
                  (all-dargp-less-than dargs dag-len)
                  ;;(equal (len dargs) (len terms))
                  (not (equal :fail (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)))
                  (term-skeletons-match-dagp terms dargs dag-array))
             (all-dargp-less-than (strip-cdrs (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)) dag-len))
    :flag unify-terms-and-dag-when-skeleton-correct)
  :hints (("Goal" :expand ((UNIFY-TERMS-AND-DAG-WHEN-SKELETON-CORRECT TERMS dargs DAG-ARRAY DAG-LEN ALIST))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable INTEGERP-OF-CAR-WHEN-ALL-DARGP
                              term-skeleton-matches-dagp
                              term-skeletons-match-dagp
                              unify-term-and-dag-when-skeleton-correct
                              unify-terms-and-dag-when-skeleton-correct))))

(defthm-flag-unify-term-and-dag-when-skeleton-correct
  (defthm all-dargp-of-strip-cdrs-of-unify-term-and-dag-when-skeleton-correct
    (implies (and (all-dargp (strip-cdrs alist))
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-termp term)
                  (dargp-less-than darg dag-len)
                  (not (equal :fail (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist)))
                  (term-skeleton-matches-dagp term darg dag-array))
             (all-dargp (strip-cdrs (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len alist))))
    :flag unify-term-and-dag-when-skeleton-correct)
  (defthm all-dargp-of-strip-cdrs-of-unify-terms-and-dag-when-skeleton-correct
    (implies (and (all-dargp (strip-cdrs alist))
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (alistp alist)
                  ;;(pseudo-term-listp terms)
                  (all-dargp-less-than dargs dag-len)
                  ;;(equal (len dargs) (len terms))
                  (not (equal :fail (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist)))
                  (term-skeletons-match-dagp terms dargs dag-array))
             (all-dargp (strip-cdrs (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len alist))))
    :flag unify-terms-and-dag-when-skeleton-correct)
  :hints (("Goal" :expand ((UNIFY-TERMS-AND-DAG-WHEN-SKELETON-CORRECT TERMS dargs DAG-ARRAY DAG-LEN ALIST))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable INTEGERP-OF-CAR-WHEN-ALL-DARGP
                              term-skeleton-matches-dagp
                              term-skeletons-match-dagp
                              unify-term-and-dag-when-skeleton-correct
                              unify-terms-and-dag-when-skeleton-correct))))

;;;
;;; unify-term-and-dag-item-fast (a version that fails fast if the skeletons differ)
;;;

; Returns :fail or an alist giving values to all the variables in TERM.  Attempts to fail fast.
(defund unify-term-and-dag-item-fast (term darg dag-array dag-len)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than darg dag-len))
                  :guard-hints (("Goal" :use (:instance <-of-largest-non-quotep
                                                        (args darg)
                                                        (nodenum dag-len))
                                 :in-theory (disable <-of-largest-non-quotep)))))
  (if (term-skeleton-matches-dagp term darg dag-array) ;quick check that does no consing
      (unify-term-and-dag-when-skeleton-correct term darg dag-array dag-len nil)
    :fail))

; Returns :fail or an alist giving values to all the variables in TERMS.  Attempts to fail fast.
(defund unify-terms-and-dag-items-fast (terms dargs dag-array dag-len)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (true-listp dargs)
                              (all-dargp-less-than dargs dag-len)
                              ;; (same-lengthp terms dargs) ;; should be true, but we don't want the caller to have to ensure this
                              )
                  :guard-hints (("Goal" :use (:instance <-of-largest-non-quotep
                                                        (args dargs)
                                                        (nodenum dag-len))
                                 :in-theory (disable <-of-largest-non-quotep)))))
  (if (term-skeletons-match-dagp terms dargs dag-array) ;quick check that does no consing
      (unify-terms-and-dag-when-skeleton-correct terms dargs dag-array dag-len nil)
    :fail))

(defthm all-dargp-of-strip-cdrs-of-unify-terms-and-dag-items-fast
  (implies (and (not (equal :fail (unify-terms-and-dag-items-fast terms dargs dag-array dag-len)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-dargp-less-than dargs dag-len)
                ;; (equal (len dargs)
                ;;        (len terms))
                )
           (all-dargp (strip-cdrs (unify-terms-and-dag-items-fast terms dargs dag-array dag-len))))
  :hints (("Goal" :in-theory (enable unify-terms-and-dag-items-fast))))

(defthm all-dargp-less-than-of-strip-cdrs-of-unify-terms-and-dag-items-fast
  (implies (and (not (equal :fail (unify-terms-and-dag-items-fast terms dargs dag-array dag-len)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-dargp-less-than dargs dag-len)
                ;; (equal (len dargs)
                ;;        (len terms))
                )
           (all-dargp-less-than (strip-cdrs (unify-terms-and-dag-items-fast terms dargs dag-array dag-len))
                                           dag-len))
  :hints (("Goal" :in-theory (enable unify-terms-and-dag-items-fast))))

(defthm symbol-alistp-of-unify-terms-and-dag-items-fast
  (implies (and (pseudo-term-listp terms)
                (not (equal :fail (unify-terms-and-dag-items-fast terms dargs dag-array dag-len))))
           (symbol-alistp (unify-terms-and-dag-items-fast terms dargs dag-array dag-len)))
  :hints (("Goal" :in-theory (enable unify-terms-and-dag-items-fast))))

(defthm true-listp-of-unify-terms-and-dag-items-fast
  (implies (and (pseudo-term-listp terms) ;drop?
                (not (equal :fail (unify-terms-and-dag-items-fast terms dargs dag-array dag-len))))
           (true-listp (unify-terms-and-dag-items-fast terms dargs dag-array dag-len)))
  :hints (("Goal" :use (:instance symbol-alistp-of-unify-terms-and-dag-items-fast)
           :in-theory (disable symbol-alistp-of-unify-terms-and-dag-items-fast))))
