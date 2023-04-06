; Utilities for dealing with untranslated terms
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This book includes some utilities for dealing with untranslated terms, so
;; that we don't have the translate them, process them, and then try to
;; untranslate them (which can lose information, especially non-logical
;; information related to, e.g., execution).  The set of macros we will have to
;; support is unfortunately open-ended.  We currently support let, let*, b*
;; (partially), cond, case, and case-match.

;; TODO: Add support for flet and macrolet.

;; See also the other files in this dir, which reflect a newer approach.

;; TODO: Add support for expanding away any macros for which we do not have
;; special handling (e.g., calls of b* with b* binders that we do not yet
;; handle).  Or perhaps many (hygienic?) macros can just be treated like
;; function calls for many purposes (e.g., when replacing variables with new
;; terms in a term).

;; TODO: Replace more of the hand-written functions with calls to def-untranslated-term-fold

(include-book "untranslated-constantp")
(include-book "untranslated-variablep")
(include-book "cond-helpers")
(include-book "bstar-helpers")
(include-book "case-helpers")
(include-book "case-match-helpers")
(include-book "let-helpers")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system)
(include-book "kestrel/utilities/map-symbol-name" :dir :system)
(include-book "kestrel/utilities/legal-variable-listp" :dir :system)
(include-book "kestrel/utilities/lambdas" :dir :system)
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "std/alists/remove-assocs" :dir :system) ; todo: use clear-keys
(include-book "std/util/bstar" :dir :system) ; redundant but included because this book "knows" about b*
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (in-theory (disable butlast
                           legal-variablep
                           symbol-alistp
                           mv-nth)))

;;=== stuff to move to libraries:

(defthm legal-case-clausesp-of-make-doublets
  (implies (legal-case-clausesp clauses)
           (legal-case-clausesp (make-doublets (strip-cars clauses) terms)))
  :hints (("Goal" :induct (make-doublets clauses terms)
           :in-theory (enable make-doublets legal-case-clausesp))))

;; ;; Test for a list of non-dotted pairs
;; ;TODO: Aren't these doublets?
;; ;drop?
;; (defund pair-listp (pairs)
;;   (declare (xargs :guard t))
;;   (if (atom pairs)
;;       (equal nil pairs)
;;     (and (eql 2 (len (car pairs)))
;;          (pair-listp (cdr pairs)))))

;; (defthm alistp-when-pair-listp-cheap
;;   (implies (PAIR-LISTP x)
;;            (alistp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable pair-listp))))

;; (defthmd all->=-len-when-pair-listp
;;   (implies (pair-listp x)
;;            (all->=-len x 2))
;;   :hints (("Goal" :in-theory (enable pair-listp))))

;; (defthm ALL->=-LEN-when-pair-listp-cheap
;;   (implies (PAIR-LISTP x)
;;            (ALL->=-LEN x 2))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable pair-listp))))

;; (defthm acl2-count-of-strip-cars-when-pair-listp
;;   (implies (and (pair-listp x)
;;                 (consp x))
;;            (< (acl2-count (strip-cars x))
;;               (acl2-count x)))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable pair-listp))))

;; (defthm acl2-count-of-strip-cadrs-when-pair-listp
;;   (implies (and (pair-listp x)
;;                 (consp x))
;;            (< (acl2-count (strip-cadrs x))
;;               (acl2-count x)))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable pair-listp))))

(defthm <=-of-acl2-count-of-strip-cadrs-linear
  (<= (acl2-count (strip-cadrs x))
      (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable strip-cadrs))))

(defthmd car-of-last-when-len-is-1
  (implies (equal 1 (len x))
           (equal (CAR (LAST x))
                  (car x)))
  :hints (("Goal" :expand ((LEN (CDR X)))
           :in-theory (enable last (:i len)))))

(defthmd acl2-count-of-car-lemma
  (implies (<= (acl2-count term1) (acl2-count term2))
           (equal (< (acl2-count (car term1))
                     (acl2-count term2))
                  (if (consp term1)
                      t
                    (< 0
                       (acl2-count term2))))))

(defthmd acl2-count-of-cdr-lemma
  (implies (<= (acl2-count term1) (acl2-count term2))
           (equal (< (acl2-count (cdr term1))
                     (acl2-count term2))
                  (if (consp term1)
                      t
                    (< 0
                       (acl2-count term2))))))

;; ;todo: replace pair-listp with something standard:
;; (defthm pair-listp-of-make-doublets
;;   (pair-listp (make-doublets x y))
;;   :hints (("Goal" :in-theory (enable pair-listp make-doublets))))

;todo: looped with LIST::LEN-WHEN-AT-MOST-1
(defthmd consp-when-len-known
  (implies (and (equal free (len x))
;                (syntaxp (quotep free))
                (posp free) ;gets evaluated
                )
           (consp x)))

(defthm ulambda-formals-of-make-ulambda
  (equal (ulambda-formals (make-ulambda formals declares body))
         formals)
  :hints (("Goal"
           :in-theory (enable make-ulambda ulambda-formals))))

;; Sanity check: Nothing can be an untranslated-constant and an
;; untranslated-variable.
(defthm not-and-of-untranslated-constantp-and-untranslated-variablep
  (not (and (untranslated-constantp x)
            (untranslated-variablep x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable untranslated-variablep
                                     untranslated-constantp
                                     legal-variablep
                                     legal-variable-or-constant-namep))))

;; end of library lemmas

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion

 ;; test for (lambda (...vars...) ...declares... body)
 ;; Example with (two!) declares: (lambda (x y) (declare (ignore y)) (declare (ignore y)) (+ x))
 (defun untranslated-lambda-exprp (expr)
   (declare (xargs :guard t
                   :hints (("Goal" :in-theory (enable ulambda-body)))))
   (and (call-of 'lambda expr)
        (true-listp (fargs expr))
        (<= 2 (len (fargs expr)))
        (symbol-listp (ulambda-formals expr)) ;the lambda is not necessarily closed (as it will be once translated)!
        ;todo: check the declares?
        (untranslated-termp (ulambda-body expr))))

 ;; ttodo: add support for mv-let, and more constructs.
 ;; This allows macro calls that look like function calls, even if the macros are unknown.
 ;; NOTE: Keep in sync with *supported-untranslated-term-macros*.
 (defun untranslated-termp (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (or (untranslated-constantp x)
       (untranslated-variablep x)
       (and (consp x)
            (true-listp (fargs x)) ; also checked below in some cases, but convenient to have here
            (let ((fn (ffn-symb x))) ;todo: what are the legal FNs?
              (case fn
                ((let let*) ; (let/let* <bindings> ...declares... <body>)
                 (and (<= 2 (len (fargs x))) ; must have bindings and body
                      (let ((bindings (let-bindings x)) ; todo, if let, check for no duplicate bindings?
                            (body (let-body x)))
                        (and (legal-let-bindingsp bindings)
                             (untranslated-term-listp (let-binding-terms bindings))
                             ;;declares can intervene - todo: check their form
                             (untranslated-termp body)))))
                (b* ;;(b* <bindings> <result-form>+)
                    (let ((bindings (farg1 x))
                          (result-forms (rest (fargs x))))
                      (and (supported-b*-bindingsp bindings)
                           (untranslated-term-listp (extract-terms-from-b*-bindings bindings))
                           (untranslated-term-listp result-forms))))
                (cond ; (cond ...clauses...)
                 (let ((clauses (fargs x)))
                   (and (legal-cond-clausesp clauses)
                        (untranslated-term-listp (extract-terms-from-cond-clauses clauses)))))
                (case ; (case expr ...pairs...)
                  (let ((expr (farg1 x))
                        (pairs (cdr (fargs x))))
                    (and (untranslated-termp expr)
                         (legal-case-clausesp pairs)
                         (untranslated-term-listp (strip-cadrs pairs)))))
                (case-match ; (case-match sym ...cases...)
                  (let* ((sym (farg1 x))
                         (cases (rest (fargs x))))
                    (and (symbolp sym) ; non-var symbols, such as nil, :foo, and *c*, are also allowed
                         (untranslated-termp sym)
                         (legal-case-match-casesp cases)
                         (untranslated-term-listp (extract-terms-from-case-match-cases cases)))))
                (quote nil) ;; disallow quotes not covered by the untranslated-constantp call above
                (otherwise
                 ;;regular function call or macro call or lambda application:
                 (and (untranslated-term-listp (fargs x)) ;;first check the args
                      (or (symbolp fn)
                          (and (untranslated-lambda-exprp fn)
                               (equal (len (ulambda-formals fn))
                                      (len (fargs x))))))))))))

 (defun untranslated-term-listp (terms)
   (declare (xargs :guard t :measure (acl2-count terms)))
   (if (not (consp terms))
       (null terms)
     (and (untranslated-termp (car terms))
          (untranslated-term-listp (cdr terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *supported-untranslated-term-macros* '(let let* b* cond case case-match))

;; Do we still need this?
(defthm untranslated-termp-of-cons
  (equal (untranslated-termp (cons x y))
         (and (true-listp y)
              (if (eq 'quote x)
                  (and (true-listp y)
                       (equal 1 (len y)))
                (if (member-eq x '(let let*))
                    (and (true-listp y)
                         (<= 2 (len y)) ; must have bindings and body
                         (let ((bindings (let-bindings (cons x y))) ; todo, if let, check for no duplicate bindings?
                               (body (let-body (cons x y))))
                           (and (legal-let-bindingsp bindings)
                                (untranslated-term-listp (let-binding-terms bindings))
                                ;;declares can intervene - todo: check their form
                                (untranslated-termp body))))
                  (if (eq 'b* x)
                      (and (true-listp y)
                           (let ((bindings (first y))
                                 (result-forms (rest y)))
                             (and (supported-b*-bindingsp bindings)
                                  (untranslated-term-listp (extract-terms-from-b*-bindings bindings))
                                  (untranslated-term-listp result-forms))))
                    (if (eq 'cond x)
                        (and (legal-cond-clausesp y)
                             (untranslated-term-listp (extract-terms-from-cond-clauses y)))
                      (if (eq x 'case)
                          (and (true-listp y)
                               (let ((expr (car y))
                                     (pairs (cdr y)))
                                 (and (untranslated-termp expr)
                                      (legal-case-clausesp pairs)
                                      (untranslated-term-listp (strip-cadrs pairs)))))
                        (if (eq x 'case-match)
                            (and (true-listp y)
                                 (let* ((sym (car y))
                                        (cases (cdr y)))
                                   (and (symbolp sym)
                                        (untranslated-termp sym)
                                        (legal-case-match-casesp cases)
                                        (untranslated-term-listp (extract-terms-from-case-match-cases cases)))))
                          (and (untranslated-term-listp y)
                               (or (symbolp x)
                                   (and (untranslated-lambda-exprp x)
                                        (equal (len (ulambda-formals x))
                                               (len y))))))))))))))

;; Needed for untranslated-termp-of-cons-normal-case
(defthm untranslated-term-listp-forward-to-true-listp
  (implies (untranslated-term-listp terms)
           (true-listp terms))
  :rule-classes :forward-chaining)

(defthm untranslated-termp-of-cons-normal-case
  (implies (and (symbolp fn)
                (not (member-equal fn *supported-untranslated-term-macros*))
                (not (equal fn 'quote)))
           (equal (untranslated-termp (cons fn args))
                  (untranslated-term-listp args)))
  :hints (("Goal" :expand (untranslated-termp (cons fn args))
           :in-theory (enable member-equal))))

(defthm untranslated-termp-forward-to-true-listp
  (implies (and (untranslated-termp term)
                (consp term))
           (true-listp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable untranslated-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about untranslated-term-listp

(defthm untranslated-termp-of-car-when-untranslated-term-listp
  (implies (and (untranslated-term-listp terms)
                (consp terms))
           (untranslated-termp (car terms)))
  :hints (("Goal" :in-theory (enable untranslated-term-listp))))

(defthm untranslated-term-listp-of-cdr-when-untranslated-term-listp
  (implies (and (untranslated-term-listp terms)
                (consp terms))
           (untranslated-term-listp (cdr terms)))
  :hints (("Goal" :in-theory (enable untranslated-term-listp))))

(defthm untranslated-term-listp-of-take
  (implies (untranslated-term-listp x)
           (untranslated-term-listp (take n x)))
  :hints (("Goal" :in-theory (e/d (untranslated-term-listp take)
                                  (;take-of-cdr-becomes-subrange
                                   )))))

(defthm untranslated-termp-of-cadr
  (implies (and (untranslated-term-listp terms)
                (<= 2 (len terms)))
           (untranslated-termp (cadr terms))))

(defthm untranslated-termp-of-car-of-last-gen
  (implies (untranslated-term-listp terms)
           (untranslated-termp (car (last terms))))
  :hints (("Goal" :in-theory (enable last))))

(defthm untranslated-term-listp-of-remove-equal
  (implies (untranslated-term-listp x)
           (untranslated-term-listp (remove-equal a x))))

(defthm untranslated-term-listp-of-nthcdr
  (implies (untranslated-term-listp x)
           (untranslated-term-listp (nthcdr n x))))

(defthm untranslated-term-listp-of-append
  (equal (untranslated-term-listp (append x y))
         (and (untranslated-term-listp (true-list-fix x))
              (untranslated-term-listp y)))
  :hints (("Goal" :in-theory (enable append))))

;; Disable for speed
(defthmd true-listp-when-untranslated-term-listp
  (implies (untranslated-term-listp terms)
           (true-listp terms))
  :hints (("Goal" :in-theory (enable untranslated-term-listp))))

(local (in-theory (enable true-listp-when-untranslated-term-listp)))


(defthm untranslated-termp-when-legal-variablep-cheap
  (implies (legal-variablep x)
           (untranslated-termp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable untranslated-termp
                                     untranslated-variablep))))

(defthm untranslated-term-listp-when-legal-variable-listp-cheap
  (implies (legal-variable-listp x)
           (untranslated-term-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable legal-variable-listp))))




(defthm untranslated-termp-of-ulambda-body
  (implies (untranslated-lambda-exprp lambda)
           (untranslated-termp (ulambda-body lambda)))
  :hints (("Goal" :expand (untranslated-lambda-exprp lambda)
           :in-theory (enable ulambda-body untranslated-lambda-exprp))))

(defthm untranslated-lambda-exprp-of-make-ulambda
  (equal (untranslated-lambda-exprp (make-ulambda formals declares body))
         (and (symbol-listp formals)
              (untranslated-termp body)))
  :hints (("Goal"
           :in-theory (enable make-ulambda untranslated-lambda-exprp ulambda-body ulambda-formals))))

(defthm untranslated-termp-of-let-body
  (implies (and (untranslated-termp term)
                (member-equal (car term) '(let let*)))
           (untranslated-termp (let-body term)))
  :hints (("Goal" :expand ((untranslated-termp term)))))

(local (in-theory (enable UNTRANSLATED-TERMP))) ; drop?

(defthm untranslated-termp-of-cdr-of-assoc-equal
  (implies (and (assoc-equal key alist)
                (untranslated-term-listp (strip-cdrs alist)))
           (untranslated-termp (cdr (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun symbol-or-untranslated-lambda-exprp (item)
  (declare (xargs :guard t))
  (or (symbolp item)
      (untranslated-lambda-exprp item)))

(defun all-symbol-or-untranslated-lambda-exprp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (symbol-or-untranslated-lambda-exprp (first x))
         (all-symbol-or-untranslated-lambda-exprp (rest x)))))

;(in-theory (disable untranslated-lambda-exprp))

 ;; test for ((lambda (...vars...) ...declares... body) ...args...)
;; (defun untranslated-lambda-applicationp (expr)
;;   (declare (xargs :guard t))
;;   (and (consp expr)
;;        (untranslated-lambda-exprp (ffn-symb expr))
;;        (untranslated-term-listp (fargs expr))))


;; (defthm UNTRANSLATED-TERM-PAIRSP-of-cadr
;;   (IMPLIES (AND (UNTRANSLATED-TERMP TERM)
;;                 (EQUAL (CAR TERM) 'B*))
;;            (UNTRANSLATED-TERM-PAIRSP (CADR TERM)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
;;   :hints (("Goal" :expand ((UNTRANSLATED-TERMP TERM))
;;            )))

(defthm untranslated-term-listp-of-extract-terms-from-cond-clauses-of-recreate-cond-clauses
  (implies (untranslated-term-listp new-terms)
           (untranslated-term-listp (extract-terms-from-cond-clauses (recreate-cond-clauses clauses new-terms))))
  :hints (("Goal" :in-theory (enable extract-terms-from-cond-clauses recreate-cond-clauses))))

(defthm untranslated-term-listp-of-extract-terms-from-b*-binding-of-mv-nth-0-of-recreate-b*-binding
  (implies (and (supported-b*-bindingp binding)
                (untranslated-term-listp new-terms))
           (untranslated-term-listp (extract-terms-from-b*-binding (mv-nth 0 (recreate-b*-binding binding new-terms)))))
  :hints (("Goal" :in-theory (enable recreate-b*-binding extract-terms-from-b*-binding))))

(defthm untranslated-term-listp-of-mv-nth-1-of-recreate-b*-binding
  (implies (and ;(supported-b*-bindingp binding)
                (untranslated-term-listp new-terms))
           (untranslated-term-listp (mv-nth 1 (recreate-b*-binding binding new-terms))))
  :hints (("Goal" :in-theory (enable recreate-b*-binding extract-terms-from-b*-binding))))

(defthm untranslated-term-listp-of-extract-terms-from-b*-bindings-of-recreate-b*-bindings
  (implies (and (supported-b*-bindingsp bindings)
                (untranslated-term-listp new-terms))
           (untranslated-term-listp (extract-terms-from-b*-bindings (recreate-b*-bindings bindings new-terms))))
  :hints (("Goal" :in-theory (enable extract-terms-from-b*-bindings
                                     supported-b*-bindingsp
                                     recreate-b*-bindings))))

(defthm untranslated-term-listp-of-extract-terms-from-case-match-cases-of-recreate-case-match-cases
  (implies (and (legal-case-match-casesp cases)
                (untranslated-term-listp new-terms))
           (untranslated-term-listp (extract-terms-from-case-match-cases (recreate-case-match-cases cases new-terms))))
  :hints (("Goal" :in-theory (enable extract-terms-from-case-match-cases
                                     recreate-case-match-cases
                                     legal-case-match-casesp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This one cannot be replaced with a call to def-untranslated-term-fold because it is used to define it!
(mutual-recursion
 ;;rename all function calls in TERM according to ALIST
 (defun rename-fns-in-untranslated-term (term alist)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;; (let <bindings> ...declares... <body>)
             (let ((bindings (let-bindings term))
                   (declares (let-declares term))
                   (body (let-body term)))
               `(,fn ,(make-let-bindings (let-binding-vars bindings) (rename-fns-in-untranslated-term-list (let-binding-terms bindings) alist))
                     ,@declares ;; I think these can only be IGNORE declares, so nothing to do here.
                     ,(rename-fns-in-untranslated-term body alist)))
           (if (eq fn 'b*) ;; (b* <bindings> ...result-forms...)
               (let* ((bindings (farg1 term))
                      (result-forms (rest (fargs term)))
                      (terms (extract-terms-from-b*-bindings bindings))
                      (new-terms (rename-fns-in-untranslated-term-list terms alist))
                      (new-bindings (recreate-b*-bindings bindings new-terms)))
                 `(b* ,new-bindings
                    ,@(rename-fns-in-untranslated-term-list result-forms alist)))
             (if (eq 'cond fn) ; (cond ...clauses...)
                 (let* ((clauses (fargs term))
                        (terms (extract-terms-from-cond-clauses clauses))
                        (new-terms (rename-fns-in-untranslated-term-list terms alist)))
                   `(cond ,@(recreate-cond-clauses clauses new-terms)))
               (if (eq fn 'case) ;; (case <expr> ...pairs...)
                   (let* ((expr (farg1 term))
                          (pairs (cdr (fargs term)))
                          (vals-to-match (strip-cars pairs))
                          (vals-to-return (strip-cadrs pairs)))
                     `(case ,(rename-fns-in-untranslated-term expr alist)
                        ,@(make-doublets vals-to-match
                                         (rename-fns-in-untranslated-term-list vals-to-return alist))))
                 (if (eq fn 'case-match) ; (case-match sym ...cases...)
                     (let* ((sym (farg1 term)) ; must be a symbol
                            (cases (rest (fargs term)))
                            (terms-from-cases (extract-terms-from-case-match-cases cases))
                            (new-terms-from-cases (rename-fns-in-untranslated-term-list terms-from-cases alist))
                            (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                       `(case-match ,sym ; no change since it's a symbol
                          ,@new-cases))
                   (let* ((args (fargs term))
                          (args (rename-fns-in-untranslated-term-list args alist))
                          (fn (if (consp fn)
                                  ;; ((lambda <formals> ...declares... <body>) ...args...)
                                  ;;if it's a lambda application, replace calls in the body:
                                  (let* ((lambda-formals (ulambda-formals fn))
                                         (declares (ulambda-declares fn))
                                         (lambda-body (ulambda-body fn))
                                         (new-lambda-body (rename-fns-in-untranslated-term lambda-body alist))
                                         (new-fn (make-ulambda lambda-formals declares new-lambda-body)))
                                    new-fn)
                                ;;if it's not a lambda:
                                (if (assoc-eq fn alist)
                                    (lookup-eq fn alist) ;optimize!
                                  fn))))
                     (cons fn args)))))))))))

 ;;rename all functions calls in TERMS according to ALIST
 (defun rename-fns-in-untranslated-term-list (terms alist)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (symbol-alistp alist))))
   (if (endp terms)
       nil
     (cons (rename-fns-in-untranslated-term (first terms) alist)
           (rename-fns-in-untranslated-term-list (rest terms) alist)))))

(defthm true-listp-of-rename-fns-in-untranslated-term-list
  (true-listp (rename-fns-in-untranslated-term-list terms alist)))

(defthm len-of-rename-fns-in-untranslated-term-list
  (equal (len (rename-fns-in-untranslated-term-list terms alist))
         (len terms))
  :hints (("Goal" :in-theory (enable rename-fns-in-untranslated-term-list (:i len)))))

;; (defthm untranslated-term-pairsp-of-cdr
;;   (implies (and (untranslated-termp term)
;;                 (equal 'cond (car term)))
;;            (untranslated-term-pairsp (cdr term))))

;drop?
(defthm untranslated-termp-forward-to-alistp-of-cddr-when-case
  (implies (and (untranslated-termp term)
                (eq (car term) 'case))
           (alistp (cddr term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand (untranslated-termp term))))

;drop?
(defthm untranslated-termp-forward-to-alistp-of-cddr-when-case-match
  (implies (and (untranslated-termp term)
                (eq (car term) 'case-match))
           (alistp (cddr term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand (untranslated-termp term))))

;; (defthm pat-untranslated-term-pairsp-of-cddr
;;   (implies (and (untranslated-termp term)
;;                 (member-eq (car term) '(case case-match)))
;;            (pat-untranslated-term-pairsp (cddr term)))
;;   :hints (("Goal" :in-theory (enable member-equal))))

(defthm case-match-untranslated-termp-cadr
  (implies (and (untranslated-termp term)
                (member-eq (car term) '(case case-match)))
           (untranslated-termp (cadr term)))
  :hints (("Goal" :in-theory (enable member-equal))))

; todo: use an accessor
;why do we need this
;; (defthm alistp-of-cadr-when-untranslated-termp
;;   (implies (and (untranslated-termp term)
;;                 (equal (car term) 'b*))
;;            (alistp (cadr term)))
;;   :hints (("Goal" :expand (UNTRANSLATED-TERMP TERM))))

;why do we need this
;; (defthm all->=-len-of-cadr-when-untranslated-termp
;;   (implies (and (untranslated-termp term)
;;                 (equal (car term) 'b*))
;;            (all->=-len (cadr term) 2))
;;   :hints (("Goal" :expand (untranslated-termp term))))

;; (defthm untranslated-term-listp-of-strip-cadrs-when-b*
;;   (implies (and (equal (car term) 'b*)
;;                 (untranslated-termp term))
;;            (untranslated-term-listp (strip-cadrs (cadr term))))
;;   :hints (("Goal" :expand (untranslated-termp term))))

;; (defthm untranslated-term-listp-of-cddr
;;   (implies (and (equal (car term) 'b*)
;;                 (untranslated-termp term))
;;            (untranslated-term-listp (cddr term)))
;;   :hints (("Goal" :expand (untranslated-termp term))))

(defthm untranslated-term-listp-of-cdr-2
  (implies (and (untranslated-termp term)
                (consp term)
                (not (equal 'quote (car term)))
                (not (member-eq (car term) '(let let*)))
                (not (equal (car term) 'b*))
                (not (equal 'cond (car term)))
                (not (member-eq (car term) '(case case-match))))
           (untranslated-term-listp (cdr term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm untranslated-lambda-exprp-of-car
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (untranslated-lambda-exprp (car term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(local (in-theory (disable let-declares)))

;; (defthm untranslated-termp-of-caddr-of-car
;;   (implies (and (untranslated-termp term)
;;                 (consp term)
;;                 (consp (car term)))
;;            (untranslated-termp (CADDR (CAR TERM))))
;;   :hints (("Goal" :expand (untranslated-termp term))))

;slow?
;why are the cars and cdrs getting exposed?
(defthm consp-of-cddr-of-car-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (consp (cddr (car term))))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthmd cdr-of-car-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (cdr (car term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm consp-of-cdr-of-car-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (consp (cdr (car term))))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm true-listp-of-car-when-UNTRANSLATED-TERMP
  (IMPLIES (AND (UNTRANSLATED-TERMP TERM)
                (CONSP (CAR TERM))
                )
           (TRUE-LISTP (CAR TERM)))
  :hints (("Goal" :expand (untranslated-termp term))))

(verify-guards rename-fns-in-untranslated-term
  :hints (("Goal" :expand ((UNTRANSLATED-TERMP TERM))
           :in-theory (e/d ( ;untranslated-lambda-exprp ;UNTRANSLATED-TERMP
                            )
                           (UNTRANSLATED-TERM-LISTP
                            UNTRANSLATED-TERMP
                            ALISTP)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 ;;Return a list of all functions called in TERM
 (defun get-called-fns-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       nil
     (if (fquotep term)
         nil
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (let ((bindings (let-bindings term))
                   (body (let-body term)))
               (union-eq (get-called-fns-in-untranslated-term-list (let-binding-terms bindings))
                         (get-called-fns-in-untranslated-term body)))
           (if (eq fn 'b*)
               (let ((bindings (farg1 term))
                     (result-forms (rest (fargs term))))
                 (union-eq (get-called-fns-in-untranslated-term-list (extract-terms-from-b*-bindings bindings))
                           (get-called-fns-in-untranslated-term-list result-forms)))
             (if (eq 'cond fn) ; (cond ...clauses...)
                 (let* ((clauses (fargs term))
                        (terms (extract-terms-from-cond-clauses clauses)))
                   (get-called-fns-in-untranslated-term-list terms))
               (if (eq fn 'case) ;; (case <expr> ...pairs...)
                   (let* ((expr (farg1 term))
                          (pairs (cdr (fargs term)))
                          ;; (vals-to-match (strip-cars pairs))
                          (vals-to-return (strip-cadrs pairs)))
                     (union-eq (get-called-fns-in-untranslated-term expr)
                               (get-called-fns-in-untranslated-term-list vals-to-return)))
                 (if (eq fn 'case-match) ; (case-match sym ...cases...)
                     (let* ( ;; (sym (farg1 term)) ; no called fns since it's a symbol
                            (cases (rest (fargs term)))
                            (terms-from-cases (extract-terms-from-case-match-cases cases))
                            )
                       (get-called-fns-in-untranslated-term-list terms-from-cases) ; todo: do we want fns from the patterns?  I think not.
                       )
                   (let ((fn-res (if (consp fn)
                                     ;;if it's a lambda application, examine the body:
                                     (get-called-fns-in-untranslated-term (ulambda-body fn))
                                   ;;if it's not a lambda:
                                   (list fn))))
                     (union-eq fn-res (get-called-fns-in-untranslated-term-list (fargs term)))))))))))))

 (defun get-called-fns-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (get-called-fns-in-untranslated-term (first terms))
               (get-called-fns-in-untranslated-term-list (rest terms))))))


(make-flag flag-get-called-fns-in-untranslated-term get-called-fns-in-untranslated-term)
(defthm-flag-get-called-fns-in-untranslated-term
  (defthm true-listp-of-get-called-fns-in-untranslated-term
    (implies (untranslated-termp term)
             (symbol-listp (get-called-fns-in-untranslated-term term)))
    :flag get-called-fns-in-untranslated-term)

  ;; (defthm true-listp-of-get-called-fns-in-cadrs-of-untranslated-term-pairs
  ;;   (implies (untranslated-term-pairsp pairs)
  ;;            (symbol-listp (get-called-fns-in-cadrs-of-untranslated-term-pairs pairs)))
  ;;   :flag get-called-fns-in-cadrs-of-untranslated-term-pairs)
  ;; (defthm true-listp-of-get-called-fns-in-untranslated-term-pairs
  ;;   (implies (untranslated-term-pairsp pairs)
  ;;            (symbol-listp (get-called-fns-in-untranslated-term-pairs pairs)))
  ;;   :flag get-called-fns-in-untranslated-term-pairs)
  ;; (defthm true-listp-of-get-called-fns-in-pat-untranslated-term-pairs
  ;;   (implies (pat-untranslated-term-pairsp pairs)
  ;;            (symbol-listp (get-called-fns-in-pat-untranslated-term-pairs pairs)))
  ;;   :flag get-called-fns-in-pat-untranslated-term-pairs)
  (defthm true-listp-of-get-called-fns-in-untranslated-term-list
    (implies (untranslated-term-listp terms)
             (symbol-listp (get-called-fns-in-untranslated-term-list terms)))
    :flag get-called-fns-in-untranslated-term-list))

(verify-guards get-called-fns-in-untranslated-term
               :otf-flg t
               :hints (("Goal" :in-theory (enable true-listp-when-symbol-listp-rewrite-unlimited))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defun beta-reduce-untranslated (lambda-expr)
;;   (declare (xargs :guard (untranslated-lambda-applicationp lambda-expr)
;;                   :guard-hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)))))
;;   (let* ((lambda-expr (ffn-symb lambda-expr))
;;          (actuals (fargs lambda-expr))
;;          (formals (second lambda-expr))
;;          ;; don't need the declares here
;;          (body (car (last lambda-expr))))
;;         (sublis-var-simple (pairlis$ formals actuals) ;;Darn.  We'll need a version of sublis-var-simple that handles untranslated terms...
;;                        body)))

(defun def-untranslated-term-fold-fn (base-name
                                      operation-on-term ;; a term with free vars FN and ARGS
                                      extra-args
                                      extra-guards
                                      stobjs
                                      program-mode)
  (let* ((term-processor-fn (pack$ base-name '-in-untranslated-term))
         (term-list-processor-fn (pack$ base-name '-in-untranslated-term-list))
;         (term-pairs-processor-fn (pack$ base-name '-in-untranslated-term-pairs))
;         (pat-term-pairs-processor-fn (pack$ base-name '-in-pat-untranslated-term-pairs))
;         (var-term-pairs-processor-fn (pack$ base-name '-in-var-untranslated-term-pairs))
         (theorems `((make-flag ,term-processor-fn)

                     (defthm ,(pack$ 'len-of- term-list-processor-fn)
                       (equal (len (,term-list-processor-fn terms ,@extra-args))
                              (len terms))
                       :hints (("Goal" :in-theory (enable (:i len)) :induct (len TERMS))))

                     (defthm ,(pack$ 'consp-of- term-list-processor-fn)
                       (equal (consp (,term-list-processor-fn terms ,@extra-args))
                              (consp terms))
                       :hints (("Goal" :expand (,term-list-processor-fn terms ,@extra-args))))

                     (,(pack$ 'defthm-flag- term-processor-fn)
                      (defthm ,(pack$ 'untranslated-termp-of- term-processor-fn)
                        (implies (and (untranslated-termp term)
                                      ,@extra-guards)
                                 (untranslated-termp (,term-processor-fn term ,@extra-args)))
                        :flag ,term-processor-fn)
                      ;; (defthm ,(pack$ 'var-untranslated-term-pairsp-of- var-term-pairs-processor-fn)
                      ;;   (implies (and (var-untranslated-term-pairsp pairs)
                      ;;                 ,@extra-guards)
                      ;;            (var-untranslated-term-pairsp (,var-term-pairs-processor-fn pairs ,@extra-args)))
                      ;;   :flag ,var-term-pairs-processor-fn)
                      ;; (defthm ,(pack$ 'untranslated-term-pairsp-of- term-pairs-processor-fn)
                      ;;   (implies (and (untranslated-term-pairsp pairs)
                      ;;                 ,@extra-guards)
                      ;;            (untranslated-term-pairsp (,term-pairs-processor-fn pairs ,@extra-args)))
                      ;;   :flag ,term-pairs-processor-fn)
                      ;; (defthm ,(pack$ 'untranslated-term-pairsp-of- pat-term-pairs-processor-fn)
                      ;;   (implies (and (pat-untranslated-term-pairsp pairs)
                      ;;                 ,@extra-guards)
                      ;;            (pat-untranslated-term-pairsp (,pat-term-pairs-processor-fn pairs ,@extra-args)))
                      ;;   :flag ,pat-term-pairs-processor-fn)
                      (defthm ,(pack$ 'untranslated-term-listp-of- term-list-processor-fn)
                        (implies (and (untranslated-term-listp terms)
                                      ,@extra-guards)
                                 (untranslated-term-listp (,term-list-processor-fn terms ,@extra-args)))
                        :flag ,term-list-processor-fn)
                      :hints (("Goal" :in-theory (enable untranslated-lambda-exprp)
                               :expand ((,term-processor-fn term ,@extra-args)))))

                     (verify-guards ,term-processor-fn
                       :hints (("Goal" :in-theory (e/d (untranslated-lambda-exprp
                                                        consp-when-len-known)
                                                       (untranslated-termp
                                                        untranslated-term-listp
                                                        ,(pack$ 'untranslated-term-listp-of- term-list-processor-fn)))
                                :do-not '(generalize eliminate-destructors)
                                :do-not-induct t
                                :use ((:instance ,(pack$ 'untranslated-term-listp-of- term-list-processor-fn) (terms (cdr term))))
                                :expand ((untranslated-term-listp (,term-list-processor-fn (cdr term) ,@extra-args))
                                         (untranslated-termp term)
                                         (untranslated-termp (car (,term-list-processor-fn (cdr term) ,@extra-args)))
                                         )))
                       :otf-flg t))))
    `(progn
       (mutual-recursion
        (defun ,term-processor-fn (term ,@extra-args)
          (declare (xargs :guard (and (untranslated-termp term) ;todo: drop the and if no extra guards
                                      ,@extra-guards)
                          :verify-guards nil ;done below
                          :hints (("Goal" :do-not-induct t))
                          :ruler-extenders :all
                          ,@(and stobjs `(:stobjs ,stobjs))
                          ,@(if program-mode '(:mode :program) nil)))
          (if (atom term)
              term
            (if (fquotep term)
                term
              ;;function call or lambda
              (let* ((fn (ffn-symb term)))
                (if (member-eq fn '(let let*)) ;;(let <bindings> <body>)
                    (let ((bindings (let-bindings term))
                          (declares (let-declares term))
                          (body (let-body term)))
                      `(,fn ,(make-let-bindings (let-binding-vars bindings)
                                                (,term-list-processor-fn (let-binding-terms bindings) ,@extra-args))
                            ,@declares
                            ,(,term-processor-fn body ,@extra-args)))
                  (if (eq fn 'b*)
                      (let* ((bindings (farg1 term))
                             (result-forms (rest (fargs term)))
                             (terms (extract-terms-from-b*-bindings bindings))
                             (new-terms (,term-list-processor-fn terms ,@extra-args))
                             (new-bindings (recreate-b*-bindings bindings new-terms)))
                        `(b* ,new-bindings
                           ,@(,term-list-processor-fn result-forms ,@extra-args)))
                    (if (eq 'cond fn) ; (cond ...clauses...)
                        (let* ((clauses (fargs term))
                               (terms (extract-terms-from-cond-clauses clauses))
                               (new-terms (,term-list-processor-fn terms ,@extra-args)))
                          `(cond ,@(recreate-cond-clauses clauses new-terms)))
                      ;; function call (possibly a lambda):
                      (if (eq fn 'case) ;; (case <expr> ...pairs...)
                          (let* ((expr (farg1 term))
                                 (pairs (cdr (fargs term)))
                                 (vals-to-match (strip-cars pairs))
                                 (vals-to-return (strip-cadrs pairs)))
                            `(case ,(,term-processor-fn expr ,@extra-args)
                               ,@(make-doublets vals-to-match
                                                (,term-list-processor-fn vals-to-return ,@extra-args))))
                        (if (eq fn 'case-match) ; (case-match sym ...cases...)
                            (b* ((sym (farg1 term))
                                 (cases (rest (fargs term)))
                                 (new-sym (,term-processor-fn sym ,@extra-args))
                                 ((when (not (and (symbolp new-sym)
                                                  (untranslated-termp new-sym)))) ; todo: could let-bind a new var, for use in the case-match?
                                  (er hard? ',term-processor-fn "Attempt to create a case-match whose first argument is ~x0, which is not a legal symbol." new-sym))
                                 (terms-from-cases (extract-terms-from-case-match-cases cases))
                                 (new-terms-from-cases (,term-list-processor-fn terms-from-cases ,@extra-args))
                                 (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                              `(case-match ,new-sym
                                 ,@new-cases))
                          (let* ((args (fargs term))
                                 (args (,term-list-processor-fn args ,@extra-args)))
                            ;; Splice in the operation to be performed, by replacing calls of :recur with calls of the term-processor function
                            ;; TODO: Support referring to the args and the arg-results?
                            ,(rename-fns-in-untranslated-term operation-on-term (acons :recur term-processor-fn nil))))))))))))

        ;; ;; TODO: Deprecate?
        ;; (defun ,var-term-pairs-processor-fn (pairs ,@extra-args)
        ;;   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
        ;;                               ,@extra-guards)
        ;;                   ,@(and stobjs `(:stobjs ,stobjs))))
        ;;   (if (endp pairs)
        ;;       nil
        ;;     (let* ((pair (first pairs))
        ;;            (var (first pair))
        ;;            (term (second pair)))
        ;;       (cons (list var (,term-processor-fn term ,@extra-args))
        ;;             (,var-term-pairs-processor-fn (rest pairs) ,@extra-args)))))

        (defun ,term-list-processor-fn (terms ,@extra-args)
          (declare (xargs :guard (and (untranslated-term-listp terms)
                                      ,@extra-guards)
                          ,@(and stobjs `(:stobjs ,stobjs))))
          (if (endp terms)
              nil
            (cons (,term-processor-fn (first terms) ,@extra-args)
                  (,term-list-processor-fn (rest terms) ,@extra-args)))))

       ;; Suppress theorems if program-mode
       ,@(and (not program-mode) theorems))))

;; Operation-on-term should be a term with free vars FN and ARGS.  It should
;; create a new untranslated term from the FN and the already-processed ARGS.
;; It can mention :recur to do a recursive call of the fold function being
;; defined.  It does nothing to atoms or quoted constants.

(defmacro def-untranslated-term-fold (base-name operation-on-term
                                                &key
                                                (extra-args 'nil)
                                                (extra-guards 'nil)
                                                (stobjs 'nil)
                                                (program-mode 'nil)
                                                )
  (def-untranslated-term-fold-fn base-name operation-on-term extra-args extra-guards stobjs program-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version does not require pseudo-terms...
;; a variant of rename-fns-in-untranslated-term that also expands lambdas that any fns get mapped to
(mutual-recursion
 ;; TODO: Do this in 2 steps?
 ;; ALIST maps function symbols to function symbols or lambdas
 (defun rename-fns-and-expand-lambdas-in-untranslated-term (term alist)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))
                   :verify-guards nil ;;done below
                   :guard-hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
                                  :expand (UNTRANSLATED-TERMP TERM)))))
   (if (atom term) ;includes variables but also things like unquoted integers
       term
     (if (fquotep term)
         term
       ;;function call or lambda/let/etc.
       (let* (;;Now all we have to do is handle the fn.  It might already be a lambda, or it might be mapped to a lambda (which should be expanded).
              (fn (ffn-symb term)))
         (if (consp fn)
             ;; it's a lambda:
             (let ((args (rename-fns-and-expand-lambdas-in-untranslated-term-lst (fargs term) alist))) ;first, apply to the args
               (if nil ;(not (lambda-exprp fn)) ;TODO: drop this check
                   (hard-error 'rename-fns-and-expand-lambdas-in-untranslated-term "Unexpected form for term ~x0." (acons #\0 term nil))
                 ;;if the original term is a lambda application, replace calls in the lambda body:
                 (let* ((lambda-formals (ulambda-formals fn))
                        (declares (ulambda-declares fn))
                        (lambda-body (ulambda-body fn))
                        (new-lambda-body (rename-fns-and-expand-lambdas-in-untranslated-term lambda-body alist))
                        (fn (make-ulambda lambda-formals declares new-lambda-body)))
                   ;; Don't try to rename the fn because it is a lambda
                   `(,fn ,@args))))
           ;;The original fn is a symbol:
           (if (member-eq fn '(let let*))
               (let ((bindings (let-bindings term))
                     (declares (let-declares term))
                     (body (let-body term)))
                 `(,fn
                   ,(make-let-bindings (let-binding-vars bindings)
                                       (rename-fns-and-expand-lambdas-in-untranslated-term-lst (let-binding-terms bindings) alist))
                   ,@declares
                   ;; the body:
                   ,(rename-fns-and-expand-lambdas-in-untranslated-term body alist)))
             (if (eq fn 'b*)
                 (let* ((bindings (farg1 term))
                        (result-forms (rest (fargs term)))
                        (terms (extract-terms-from-b*-bindings bindings))
                        (new-terms (rename-fns-and-expand-lambdas-in-untranslated-term-lst terms alist))
                        (new-bindings (recreate-b*-bindings bindings new-terms)))
                   `(b* ,new-bindings
                      ,@(rename-fns-and-expand-lambdas-in-untranslated-term-lst result-forms alist)))
               (if (eq fn 'cond) ; (cond ...clauses...)
                   (let* ((clauses (fargs term))
                          (terms (extract-terms-from-cond-clauses clauses))
                          (new-terms (rename-fns-and-expand-lambdas-in-untranslated-term-lst terms alist)))
                     `(cond ,@(recreate-cond-clauses clauses new-terms)))
                 (if (eq fn 'case) ;; (case <expr> ...pairs...)
                     (let* ((expr (farg1 term))
                            (pairs (cdr (fargs term)))
                            (vals-to-match (strip-cars pairs))
                            (vals-to-return (strip-cadrs pairs)))
                       `(case ,(rename-fns-and-expand-lambdas-in-untranslated-term expr alist)
                          ,@(make-doublets vals-to-match
                                           (rename-fns-and-expand-lambdas-in-untranslated-term-lst vals-to-return alist))))
                   (if (eq fn 'case-match) ; (case-match sym ...cases...)
                       (let* ((sym (farg1 term))
                              (cases (rest (fargs term)))
                              (terms-from-cases (extract-terms-from-case-match-cases cases))
                              (new-terms-from-cases (rename-fns-and-expand-lambdas-in-untranslated-term-lst terms-from-cases alist))
                              (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                         `(case-match ,sym ; no change since it's a symbol
                            ,@new-cases))
                     ;; regular function
                     (let ((args (rename-fns-and-expand-lambdas-in-untranslated-term-lst (fargs term) alist)) ;first, apply to the args
                           (res (assoc-eq fn alist))) ;;see if it is renamed
                       (if (not res)
                           `(,fn ,@args) ;fn isn't renamed to anything
                         (let ((fn (cdr res)))
                           (if (LAMBDA-EXPRP fn) ;; TTODO: weaken to: (consp fn) ;test for a lambda
                               ;;fn is renamed to a lambda
                               (beta-reduce ;-untranslated
                                `(,fn ,@args))
                             ;;fn is mapped to a symbol
                             `(,fn ,@args)))))))))))))))

 ;;Rename all functions called in TERMS according that are mapped to new names by ALIST.
 ;; tdo rename the lst to list
 (defun rename-fns-and-expand-lambdas-in-untranslated-term-lst (terms alist)
   (declare (xargs :guard (and (untranslated-term-listp terms) ;(true-listp terms)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))))
   (if (atom terms)
       nil
     (cons (rename-fns-and-expand-lambdas-in-untranslated-term (car terms) alist)
           (rename-fns-and-expand-lambdas-in-untranslated-term-lst (cdr terms) alist))))

 ;; ;; these are non-dotted pairs
 ;; (defun rename-fns-and-expand-lambdas-in-var-untranslated-term-pairs (pairs alist)
 ;;   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
 ;;                               (symbol-alistp alist)
 ;;                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (var (first pair))
 ;;            (term (second pair)))
 ;;       (cons (list var (rename-fns-and-expand-lambdas-in-untranslated-term term alist))
 ;;             (rename-fns-and-expand-lambdas-in-var-untranslated-term-pairs (rest pairs) alist)))))
 )

(defthm true-listp-of-rename-fns-and-expand-lambdas-in-untranslated-term-lst
  (true-listp (rename-fns-and-expand-lambdas-in-untranslated-term-lst terms alist)))

(defthm len-of-rename-fns-and-expand-lambdas-in-untranslated-term-lst
  (equal (len (rename-fns-and-expand-lambdas-in-untranslated-term-lst terms alist))
         (len terms))
  :hints (("Goal" :in-theory (enable rename-fns-in-untranslated-term-list (:i len)))))

(verify-guards rename-fns-and-expand-lambdas-in-untranslated-term
  :hints  (("Goal" :in-theory (enable untranslated-lambda-exprp)
            :expand (untranslated-termp term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;;Replace 0-ary lambda applications of the form ((lambda () <body>)) with just
;;;<body> (and apply to body recursively).
;;;

(mutual-recursion
 (defun clean-up-0ary-lambdas-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (let ((bindings (let-bindings term))
                   (declares (let-declares term))
                   (body (let-body term)))
               `(,fn ,(make-let-bindings (let-binding-vars bindings)
                                         (clean-up-0ary-lambdas-in-untranslated-term-list (let-binding-terms bindings)))
                     ,@declares
                     ,(clean-up-0ary-lambdas-in-untranslated-term body)))
           (if (eq fn 'b*)
               (let* ((bindings (farg1 term))
                      (result-forms (rest (fargs term)))
                      (terms (extract-terms-from-b*-bindings bindings))
                      (new-terms (clean-up-0ary-lambdas-in-untranslated-term-list terms))
                      (new-bindings (recreate-b*-bindings bindings new-terms)))
                 `(b* ,new-bindings
                    ,@(clean-up-0ary-lambdas-in-untranslated-term-list result-forms)))
             (if (eq 'cond fn) ; (cond ...clauses...)
                 (let* ((clauses (fargs term))
                        (terms (extract-terms-from-cond-clauses clauses))
                        (new-terms (clean-up-0ary-lambdas-in-untranslated-term-list terms)))
                   `(cond ,@(recreate-cond-clauses clauses new-terms)))
               (if (eq fn 'case) ;; (case <expr> ...pairs...)
                   (let* ((expr (farg1 term))
                          (pairs (cdr (fargs term)))
                          (vals-to-match (strip-cars pairs))
                          (vals-to-return (strip-cadrs pairs)))
                     `(case ,(clean-up-0ary-lambdas-in-untranslated-term expr)
                        ,@(make-doublets vals-to-match
                                         (clean-up-0ary-lambdas-in-untranslated-term-list vals-to-return))))
                 (if (eq fn 'case-match) ; (case-match sym ...cases...)
                     (let* ((sym (farg1 term))
                            (cases (rest (fargs term)))
                            (terms-from-cases (extract-terms-from-case-match-cases cases))
                            (new-terms-from-cases (clean-up-0ary-lambdas-in-untranslated-term-list terms-from-cases))
                            (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                       `(case-match ,sym ; no change since it's a symbol
                          ,@new-cases))
                   (if (consp fn)
                       ;;if it's a lambda application, recur on the body:
                       (let* ((lambda-formals (ulambda-formals fn))
                              (declares (ulambda-declares fn))
                              (lambda-body (ulambda-body fn))
                              (lambda-body (clean-up-0ary-lambdas-in-untranslated-term lambda-body))
                              (args (fargs term))
                              (args (clean-up-0ary-lambdas-in-untranslated-term-list args)))
                         (if (endp lambda-formals) ;test for 0-ary lambda
                             lambda-body
                           `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args)))
                     ;;regular function:
                     (cons fn (clean-up-0ary-lambdas-in-untranslated-term-list (fargs term)))))))))))))

 ;; ;;TODO: Deprecate?
 ;; (defun clean-up-0ary-lambdas-in-var-untranslated-term-pairs (pairs)
 ;;   (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (var (first pair))
 ;;            (term (second pair)))
 ;;       (cons (list var (clean-up-0ary-lambdas-in-untranslated-term term))
 ;;             (clean-up-0ary-lambdas-in-var-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-0ary-lambdas-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (cons (clean-up-0ary-lambdas-in-untranslated-term (first terms))
           (clean-up-0ary-lambdas-in-untranslated-term-list (rest terms))))))

(defthm true-listp-of-clean-up-0ary-lambdas-in-untranslated-term-list
  (true-listp (clean-up-0ary-lambdas-in-untranslated-term-list terms)))

(defthm len-of-clean-up-0ary-lambdas-in-untranslated-term-list
  (equal (len (clean-up-0ary-lambdas-in-untranslated-term-list terms))
         (len terms))
  :hints (("Goal" :in-theory (enable rename-fns-in-untranslated-term-list (:i len)))))

(verify-guards clean-up-0ary-lambdas-in-untranslated-term-list
  :hints (("Goal" :in-theory (enable untranslated-termp untranslated-termp)
           :expand ((untranslated-termp term)
                    (untranslated-lambda-exprp (car term))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;TODO: Just write a rewriter for stuff like this?
;;TODO: Could also make a macro to automate the generation of the auxiliary functions in this:
;;;
;;;Replace (implies t x) with just x.
;;;

(mutual-recursion
 (defun clean-up-implies-of-t-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
             (let ((bindings (let-bindings term))
                   (declares (let-declares term))
                   (body (let-body term)))
               `(,fn ,(make-let-bindings (let-binding-vars bindings)
                                         (clean-up-implies-of-t-in-untranslated-term-list (let-binding-terms bindings)))
                     ,@declares
                     ,(clean-up-implies-of-t-in-untranslated-term body)))
           (if (eq fn 'b*)
               (let* ((bindings (farg1 term))
                      (result-forms (rest (fargs term)))
                      (terms (extract-terms-from-b*-bindings bindings))
                      (new-terms (clean-up-implies-of-t-in-untranslated-term-list terms))
                      (new-bindings (recreate-b*-bindings bindings new-terms)))
                 `(b* ,new-bindings
                    ,@(clean-up-implies-of-t-in-untranslated-term-list result-forms)))
             (if (eq 'cond fn) ; (cond ...clauses...)
                 (let* ((clauses (fargs term))
                        (terms (extract-terms-from-cond-clauses clauses))
                        (new-terms (clean-up-implies-of-t-in-untranslated-term-list terms)))
                   `(cond ,@(recreate-cond-clauses clauses new-terms)))
               (if (eq fn 'case) ;; (case <expr> ...pairs...)
                   (let* ((expr (farg1 term))
                          (pairs (cdr (fargs term)))
                          (vals-to-match (strip-cars pairs))
                          (vals-to-return (strip-cadrs pairs)))
                     `(case ,(clean-up-implies-of-t-in-untranslated-term expr)
                        ,@(make-doublets vals-to-match
                                         (clean-up-implies-of-t-in-untranslated-term-list vals-to-return))))
                 (if (eq fn 'case-match) ; (case-match sym ...cases...)
                     (let* ((sym (farg1 term)) ; must be a symbol
                            (cases (rest (fargs term)))
                            (terms-from-cases (extract-terms-from-case-match-cases cases))
                            (new-terms-from-cases (clean-up-implies-of-t-in-untranslated-term-list terms-from-cases))
                            (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                       `(case-match ,sym ; no change since it's a symbol
                          ,@new-cases))
                   (if (consp fn)
                       ;;if it's a lambda application, recur on the body:
                       (let* ((lambda-formals (ulambda-formals fn))
                              (declares (ulambda-declares fn))
                              (lambda-body (ulambda-body fn))
                              (lambda-body (clean-up-implies-of-t-in-untranslated-term lambda-body))
                              (args (fargs term))
                              (args (clean-up-implies-of-t-in-untranslated-term-list args)))
                         `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
                     (if (and (eq fn 'implies)
                              (equal *t* (farg1 term)))
                         ;; strip off the implies of t
                         (clean-up-implies-of-t-in-untranslated-term (farg2 term))
                       ;;regular function:
                       (cons fn (clean-up-implies-of-t-in-untranslated-term-list (fargs term))))))))))))))

 ;; (defun clean-up-implies-of-t-in-var-untranslated-term-pairs (pairs)
 ;;   (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (var (first pair))
 ;;            (term (second pair)))
 ;;       (cons (list var (clean-up-implies-of-t-in-untranslated-term term))
 ;;             (clean-up-implies-of-t-in-var-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-implies-of-t-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (cons (clean-up-implies-of-t-in-untranslated-term (first terms))
           (clean-up-implies-of-t-in-untranslated-term-list (rest terms))))))

(defthm true-listp-of-clean-up-implies-of-t-in-untranslated-term-list
  (true-listp (clean-up-implies-of-t-in-untranslated-term-list terms)))

(defthm len-of-clean-up-implies-of-t-in-untranslated-term-list
  (equal (len (clean-up-implies-of-t-in-untranslated-term-list terms))
         (len terms))
  :hints (("Goal" :in-theory (enable rename-fns-in-untranslated-term-list (:i len)))))

(verify-guards clean-up-implies-of-t-in-untranslated-term-list
  :hints (("Goal" :in-theory (enable untranslated-termp untranslated-termp)
           :expand ((untranslated-termp term)
                    (untranslated-lambda-exprp (car term))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Attempt to prove that every pseudo-term is a proper untranslated-term.  It's
;; not quite true; we need to exclude the special macros LET, etc. from
;; appearing as functions in the pseudo-term.  For example: (pseudo-termp '(let
;; '3)) = t.

;(make-flag pseudo-termp)

;; A stronger version of pseudo-termp that implies untranslated-termp.
;; This disallows supported macros like LET from appearing as
;; function calls in the term.  We'll have to add things to this as we
;; add support for more constructs in untranslated-termp.

(mutual-recursion
 (defund strong-pseudo-termp (x)
   (declare (xargs :guard t :mode :logic))
   (cond ((atom x) (legal-variablep x))
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cdr (cdr x)))))
         ((member-eq (car x) *supported-untranslated-term-macros*)
          nil)
         ((not (true-listp x)) nil)
         ((not (strong-pseudo-term-listp (cdr x))) nil)
         (t (or (symbolp (car x))
                (and (true-listp (car x))
                     (equal (len (car x)) 3)
                     (eq (car (car x)) 'lambda)
                     (symbol-listp (cadr (car x)))
                     (strong-pseudo-termp (caddr (car x)))
                     (equal (len (cadr (car x)))
                            (len (cdr x))))))))
 (defund strong-pseudo-term-listp (lst)
   (declare (xargs :guard t))
   (cond ((atom lst) (equal lst nil))
         (t (and (strong-pseudo-termp (car lst))
                 (strong-pseudo-term-listp (cdr lst)))))))

(make-flag strong-pseudo-termp)

(defthm-flag-strong-pseudo-termp
  (defthmd untranslated-termp-when-strong-pseudo-termp
    (implies (strong-pseudo-termp x)
             (untranslated-termp x))
    :flag strong-pseudo-termp)
  (defthmd untranslated-term-listp-when-strong-pseudo-term-listp
    (implies (strong-pseudo-term-listp lst)
             (untranslated-term-listp lst))
    :flag strong-pseudo-term-listp)
  :hints (("Goal" :in-theory (enable car-of-last-when-len-is-1
                                     strong-pseudo-termp
                                     strong-pseudo-term-listp
                                     member-equal; todo: rule about membership in constant lists when subset
                                     ulambda-body
                                     ulambda-formals)
           :expand ((untranslated-termp x)
                    (untranslated-lambda-exprp (car x))))))

(defthm strong-pseudo-term-listp-of-firstn
  (implies (strong-pseudo-term-listp lst)
           (strong-pseudo-term-listp (firstn n lst)))
  :hints (("Goal" :in-theory (enable strong-pseudo-term-listp
                                     firstn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simplify things like (nth 3 (cons a (cons b x)))
(defun simplify-nth-of-cons (n term)
  (declare (xargs :guard (and (natp n)
                              (untranslated-termp term))))
  (if (not (call-of 'cons term))
      `(nth ,n ,term)
    (if (zp n) ;;(nth 0 (cons a x)) => a
        (farg1 term)
      ;;(nth <n> (cons a x)) => (nth <n-1> x)
      (simplify-nth-of-cons (+ -1 n) (farg2 term)))))

;(simplify-nth-of-cons 1 '(cons a (cons b x)))
;(simplify-nth-of-cons 0 '(cons a (cons b x)))
;(simplify-nth-of-cons 3 '(cons a (cons b x)))

(defthm untranslated-termp-of-simplify-nth-of-cons
  (implies (and (untranslated-termp term)
                (natp n))
           (untranslated-termp (simplify-nth-of-cons n term))))

;;TODO: Also abstract out the handling of the lambda body (usually the same, for transformations that don't mess with lambdas)
(def-untranslated-term-fold clean-up-nth-of-cons
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (and (eq 'nth fn)
             (eql 2 (len args)) ;drop?
             (or (natp (first args))
                 (and (quotep (first args))
                      (natp (unquote (first args)))))
             ;; (call-of 'cons (second args))
             ;; (eql 2 (len (fargs (second args))))
             )
        (let* ((arg1 (first args))
               (n (if (natp arg1) arg1 (unquote arg1)))
               (term (simplify-nth-of-cons n (second args))))
          term)
      ;;regular function:
      (cons fn args))))

;; (mutual-recursion
;;  (defun clean-up-nth-of-cons-in-untranslated-term (term)
;;    (declare (xargs :guard (untranslated-termp term)
;;                    :verify-guards nil ;done below
;;                    :hints (("Goal" :do-not-induct t))
;;                    :RULER-EXTENDERS :ALL
;;                    ))
;;      (if (atom term)
;;          term
;;        (if (fquotep term)
;;            term
;;          ;;function call or lambda
;;          (let* ((fn (ffn-symb term)))
;;            (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
;;                `(,fn ,(clean-up-nth-of-cons-in-var-untranslated-term-pairs (farg1 term))
;;                      ,@(butlast (rest (fargs term)) 1) ;the declares
;;                      ,(clean-up-nth-of-cons-in-untranslated-term (car (last term))))
;;              (if (eq fn 'b*)
;;                  (let* ((pairs (farg1 term))
;;                         (binders (strip-cars pairs))
;;                         (terms (strip-cadrs pairs)))
;;                    `(,fn ;,(clean-up-nth-of-cons-in-cadrs-of-untranslated-term-pairs (farg1 term))
;;                      ,(MAKE-DOUBLETS binders (clean-up-nth-of-cons-in-untranslated-term-list terms))
;;                      ,@(clean-up-nth-of-cons-in-untranslated-term-list (rest (fargs term)))))
;;                (if (eq 'cond fn) ; (cond ...clauses...)
;;                    `(,fn ,@(clean-up-nth-of-cons-in-untranslated-term-pairs (fargs term)))
;;                  ;; function call (possibly a lambda):
;;                  (let* ((args (fargs term))
;;                         (args (clean-up-nth-of-cons-in-untranslated-term-list args)))
;;                    (if (consp fn)
;;                        ;;if it's a lambda application, recur on the body:
;;                        (let* ((lambda-formals (ulambda-formals fn))
;;                               (declares (ulambda-declares fn))
;;                               (lambda-body (ulambda-body fn))
;;                               (lambda-body (clean-up-nth-of-cons-in-untranslated-term lambda-body))
;;                               )
;;                          `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
;;                      (if (and (eq 'nth fn)
;;                               (eql 2 (len args)) ;drop?
;;                               (or (natp (first args))
;;                                   (and (quotep (first args))
;;                                        (natp (unquote (first args)))))
;;                               ;; (call-of 'cons (second args))
;;                               ;; (eql 2 (len (fargs (second args))))
;;                               )
;;                          (let* ((arg1 (first args))
;;                                 (n (if (natp arg1) arg1 (unquote arg1)))
;;                                 (term (simplify-nth-of-cons n (second args))))
;;                            term)
;;                        ;;regular function:
;;                        (cons fn args)))))))))))

;;  (defun clean-up-nth-of-cons-in-var-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (var (first pair))
;;             (term (second pair)))
;;        (cons (list var (clean-up-nth-of-cons-in-untranslated-term term))
;;              (clean-up-nth-of-cons-in-var-untranslated-term-pairs (rest pairs))))))

;;  ;; ;;currently used for b* (we ignore the b* binders?)
;;  ;; (defun clean-up-nth-of-cons-in-cadrs-of-untranslated-term-pairs (pairs)
;;  ;;   (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;  ;;   (if (endp pairs)
;;  ;;       nil
;;  ;;     (let* ((pair (first pairs))
;;  ;;            (term1 (first pair))
;;  ;;            (term2 (second pair)))
;;  ;;       (cons (list term1 ;unchanged
;;  ;;                   (clean-up-nth-of-cons-in-untranslated-term term2))
;;  ;;             (clean-up-nth-of-cons-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-nth-of-cons-in-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (term1 (first pair))
;;             (term2 (second pair)))
;;        (cons (list (clean-up-nth-of-cons-in-untranslated-term term1)
;;                    (clean-up-nth-of-cons-in-untranslated-term term2))
;;              (clean-up-nth-of-cons-in-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-nth-of-cons-in-untranslated-term-list (terms)
;;    (declare (xargs :guard (untranslated-term-listp terms)))
;;    (if (endp terms)
;;        nil
;;      (cons (clean-up-nth-of-cons-in-untranslated-term (first terms))
;;            (clean-up-nth-of-cons-in-untranslated-term-list (rest terms))))))

;; (defthm TRUE-LISTP-of-CLEAN-UP-nth-of-cons-IN-UNTRANSLATED-TERM-LIST
;;   (TRUE-LISTP (CLEAN-UP-nth-of-cons-IN-UNTRANSLATED-TERM-LIST terms)))

;; ;; (verify-guards CLEAN-UP-nth-of-cons-IN-UNTRANSLATED-TERM-LIST
;; ;;   :hints (("Goal" :in-theory (enable UNTRANSLATED-TERMP UNTRANSLATED-TERMP)
;; ;;            :expand ((UNTRANSLATED-TERMP TERM)
;; ;;                     (UNTRANSLATED-LAMBDA-EXPRP (CAR TERM))))))

;; (make-flag clean-up-nth-of-cons-in-untranslated-term)

;; (defthm len-of-CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST
;;   (equal (LEN (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST terms))
;;          (LEN terms)))

;rename the theorems:
;; (defthm-flag-clean-up-nth-of-cons-in-untranslated-term
;;   (defthm theorem-for-clean-up-nth-of-cons-in-untranslated-term
;;     (implies (untranslated-termp term)
;;              (untranslated-termp (clean-up-nth-of-cons-in-untranslated-term term)))
;;     :flag clean-up-nth-of-cons-in-untranslated-term)
;;   (defthm theorem-for-clean-up-nth-of-cons-in-var-untranslated-term-pairs
;;     (implies (var-untranslated-term-pairsp pairs)
;;              (var-untranslated-term-pairsp (clean-up-nth-of-cons-in-var-untranslated-term-pairs pairs)))
;;     :flag clean-up-nth-of-cons-in-var-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-nth-of-cons-in-untranslated-term-pairs
;;     (implies (untranslated-term-pairsp pairs)
;;              (untranslated-term-pairsp (clean-up-nth-of-cons-in-untranslated-term-pairs pairs)))
;;     :flag clean-up-nth-of-cons-in-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-nth-of-cons-in-untranslated-term-list
;;     (implies (untranslated-term-listp terms)
;;              (untranslated-term-listp (clean-up-nth-of-cons-in-untranslated-term-list terms)))
;;     :flag clean-up-nth-of-cons-in-untranslated-term-list)
;;   :hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
;;            :expand ((CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM TERM)
;;                     (UNTRANSLATED-TERMP (LIST* 'B*
;;                                                (MAKE-DOUBLETS (STRIP-CARS (CADR TERM))
;;                                                            (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (STRIP-CADRS (CADR TERM))))
;;                                                (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDDR TERM))))))))

;; (defthm consp-of-clean-up-nth-of-cons-in-untranslated-term-list
;;   (equal (consp (clean-up-nth-of-cons-in-untranslated-term-list terms))
;;          (consp terms))
;;   :hints (("Goal" :expand (clean-up-nth-of-cons-in-untranslated-term-list terms))))

;; (verify-guards clean-up-nth-of-cons-in-untranslated-term
;;   :hints (("Goal" :in-theory (disable UNTRANSLATED-TERMP
;;                                       UNTRANSLATED-TERM-LISTP
;;                                       THEOREM-FOR-CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST
;;                                       )
;;            :do-not '(generalize eliminate-destructors)
;;            :do-not-induct t
;;            :use ((:instance THEOREM-FOR-CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST
;;                             (terms (cdr term))))
;;            :expand ((UNTRANSLATED-TERMP TERM)
;;                     (UNTRANSLATED-TERMP (CAR (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDR TERM))))
;;                     (UNTRANSLATED-TERM-LISTP (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDR TERM)))
;; ; (UNTRANSLATED-TERMP (CAR (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDR TERM))))
;;                     (UNTRANSLATED-LAMBDA-EXPRP (CAR TERM)))))

;;   :otf-flg t)


(defun simplify-true-listp-of-cons (term)
  (declare (xargs :guard (untranslated-termp term)))
  (if (equal nil term)
      t
    (if (equal *nil* term)
        t
      (if (not (call-of 'cons term))
          `(true-listp ,term)
        (simplify-true-listp-of-cons (farg2 term))))))

;(simplify-true-listp-of-cons 'x)
;(simplify-true-listp-of-cons 'nil)
;(simplify-true-listp-of-cons ''nil)
;(simplify-true-listp-of-cons '(cons a (cons b x)))
;(simplify-true-listp-of-cons '(cons a (cons b nil)))

;; (mutual-recursion
;;  (defun clean-up-true-listp-of-cons-in-untranslated-term (term)
;;    (declare (xargs :guard (untranslated-termp term)
;;                    :verify-guards nil ;done below
;;                    :hints (("Goal" :do-not-induct t))
;;                    :RULER-EXTENDERS :ALL
;;                    ))
;;      (if (atom term)
;;          term
;;        (if (fquotep term)
;;            term
;;          ;;function call or lambda
;;          (let* ((fn (ffn-symb term)))
;;            (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
;;                `(,fn ,(clean-up-true-listp-of-cons-in-var-untranslated-term-pairs (farg1 term))
;;                      ,@(butlast (rest (fargs term)) 1) ;the declares
;;                      ,(clean-up-true-listp-of-cons-in-untranslated-term (car (last term))))
;;              (if (eq fn 'b*)
;;                  (let* ((pairs (farg1 term))
;;                         (binders (strip-cars pairs))
;;                         (terms (strip-cadrs pairs)))
;;                    `(,fn ;,(clean-up-true-listp-of-cons-in-cadrs-of-untranslated-term-pairs (farg1 term))
;;                      ,(MAKE-DOUBLETS binders (clean-up-true-listp-of-cons-in-untranslated-term-list terms))
;;                      ,@(clean-up-true-listp-of-cons-in-untranslated-term-list (rest (fargs term)))))
;;                (if (eq 'cond fn) ; (cond ...clauses...)
;;                    `(,fn ,@(clean-up-true-listp-of-cons-in-untranslated-term-pairs (fargs term)))
;;                  ;; function call (possibly a lambda):
;;                  (let* ((args (fargs term))
;;                         (args (clean-up-true-listp-of-cons-in-untranslated-term-list args)))
;;                    (if (consp fn)
;;                        ;;if it's a lambda application, recur on the body:
;;                        (let* ((lambda-formals (ulambda-formals fn))
;;                               (declares (ulambda-declares fn))
;;                               (lambda-body (ulambda-body fn))
;;                               (lambda-body (clean-up-true-listp-of-cons-in-untranslated-term lambda-body))
;;                               )
;;                          `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
;;                      (if (and (eq 'true-listp fn)
;;                               (eql 1 (len args)) ;drop?
;;                               ;; (call-of 'cons (first args))
;;                               ;; (eql 2 (len (fargs (second args))))
;;                               )
;;                          (let* ((arg1 (first args))
;;                                 (term (simplify-true-listp-of-cons arg1)))
;;                            term)
;;                        ;;regular function:
;;                        (cons fn args)))))))))))

;;  (defun clean-up-true-listp-of-cons-in-var-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (var (first pair))
;;             (term (second pair)))
;;        (cons (list var (clean-up-true-listp-of-cons-in-untranslated-term term))
;;              (clean-up-true-listp-of-cons-in-var-untranslated-term-pairs (rest pairs))))))

;;  ;; ;;currently used for b* (we ignore the b* binders?)
;;  ;; (defun clean-up-true-listp-of-cons-in-cadrs-of-untranslated-term-pairs (pairs)
;;  ;;   (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;  ;;   (if (endp pairs)
;;  ;;       nil
;;  ;;     (let* ((pair (first pairs))
;;  ;;            (term1 (first pair))
;;  ;;            (term2 (second pair)))
;;  ;;       (cons (list term1 ;unchanged
;;  ;;                   (clean-up-true-listp-of-cons-in-untranslated-term term2))
;;  ;;             (clean-up-true-listp-of-cons-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-true-listp-of-cons-in-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (term1 (first pair))
;;             (term2 (second pair)))
;;        (cons (list (clean-up-true-listp-of-cons-in-untranslated-term term1)
;;                    (clean-up-true-listp-of-cons-in-untranslated-term term2))
;;              (clean-up-true-listp-of-cons-in-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-true-listp-of-cons-in-untranslated-term-list (terms)
;;    (declare (xargs :guard (untranslated-term-listp terms)))
;;    (if (endp terms)
;;        nil
;;      (cons (clean-up-true-listp-of-cons-in-untranslated-term (first terms))
;;            (clean-up-true-listp-of-cons-in-untranslated-term-list (rest terms))))))



;; (make-flag clean-up-true-listp-of-cons-in-untranslated-term)

;; (defthm len-of-clean-up-true-listp-of-cons-in-untranslated-term-list
;;   (equal (len (clean-up-true-listp-of-cons-in-untranslated-term-list terms))
;;          (len terms)))

;; (defthm consp-of-clean-up-true-listp-of-cons-in-untranslated-term-list
;;   (equal (consp (clean-up-true-listp-of-cons-in-untranslated-term-list terms))
;;          (consp terms))
;;   :hints (("Goal" :expand (clean-up-true-listp-of-cons-in-untranslated-term-list terms))))

;rename the theorems:
;; (defthm-flag-clean-up-true-listp-of-cons-in-untranslated-term
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-untranslated-term
;;     (implies (untranslated-termp term)
;;              (untranslated-termp (clean-up-true-listp-of-cons-in-untranslated-term term)))
;;     :flag clean-up-true-listp-of-cons-in-untranslated-term)
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-var-untranslated-term-pairs
;;     (implies (var-untranslated-term-pairsp pairs)
;;              (var-untranslated-term-pairsp (clean-up-true-listp-of-cons-in-var-untranslated-term-pairs pairs)))
;;     :flag clean-up-true-listp-of-cons-in-var-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-untranslated-term-pairs
;;     (implies (untranslated-term-pairsp pairs)
;;              (untranslated-term-pairsp (clean-up-true-listp-of-cons-in-untranslated-term-pairs pairs)))
;;     :flag clean-up-true-listp-of-cons-in-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-untranslated-term-list
;;     (implies (untranslated-term-listp terms)
;;              (untranslated-term-listp (clean-up-true-listp-of-cons-in-untranslated-term-list terms)))
;;     :flag clean-up-true-listp-of-cons-in-untranslated-term-list)
;;   :hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
;;            :expand ((CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM TERM)
;;                     (UNTRANSLATED-TERMP (LIST* 'B*
;;                                                (MAKE-DOUBLETS (STRIP-CARS (CADR TERM))
;;                                                            (CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST (STRIP-CADRS (CADR TERM))))
;;                                                (CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDDR TERM))))))))




;; (verify-guards clean-up-true-listp-of-cons-in-untranslated-term
;;   :hints (("Goal" :in-theory (e/d (UNTRANSLATED-LAMBDA-EXPRP
;;                                    consp-when-len-known)
;;                                   (UNTRANSLATED-TERMP
;;                                    UNTRANSLATED-TERM-LISTP
;;                                    THEOREM-FOR-CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST

;;                                    ))
;;            :do-not '(generalize eliminate-destructors)
;;            :do-not-induct t
;;            :use ((:instance THEOREM-FOR-CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST (terms (cdr term)))
;;                  )
;;            :expand ((UNTRANSLATED-TERMP TERM))))
;;   :otf-flg t)


(def-untranslated-term-fold
  clean-up-true-listp-of-cons
  (if (consp fn)
      ;;if it's a lambda application, recur on the body: ; todo: why does def-untranslated-term-fold not give us this?
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (and (eq 'true-listp fn)
             (eql 1 (len args)) ;drop?
             ;; (call-of 'cons (first args))
             ;; (eql 2 (len (fargs (second args))))
             )
        (let* ((arg1 (first args))
               ;; todo: does this call change the induction scheme?
               (term (simplify-true-listp-of-cons arg1)))
          term)
      ;;regular function:
      (cons fn args))))

;; Drop T from the arguments of an AND
;; introduces CLEAN-UP-AND-OF-T-IN-UNTRANSLATED-TERM
(def-untranslated-term-fold clean-up-and-of-t
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (eq 'and fn)
        (let ((args (remove-equal *t* (remove-equal 't args))))
          (if (consp args)
              `(and ,@args)
            't))
      ;;regular function:
      (cons fn args))))

(defun simplify-equality-of-len-of-cons-nest-and-number (cons-nest num)
  (declare (xargs :guard (and (UNTRANSLATED-TERMP cons-nest)
                              (integerp num))))
  (if (or (equal cons-nest nil)
          (equal cons-nest *nil*))
      (if (eql num 0)
          't
        'nil)
    (if (and (call-of 'cons cons-nest)
             (eql 2 (len (fargs cons-nest))))
        (simplify-equality-of-len-of-cons-nest-and-number (farg2 cons-nest) (+ -1 num))
      ;; nothing more to do:
      `(equal (len ,cons-nest) ,num) ;not quoting num; we are working with untranslated terms
      )))

(defthm untranslated-termp-of-simplify-equality-of-len-of-cons-nest-and-number
 (implies (and (untranslated-termp cons-nest)
               (integerp num))
          (untranslated-termp (simplify-equality-of-len-of-cons-nest-and-number cons-nest num))))

;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b x)) 2)
;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b nil)) 2)
;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b nil)) 1)
;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b nil)) 3)

;Simplify stuff like (EQUAL (LEN (CONS I (CONS J 'NIL))) 2)
(def-untranslated-term-fold clean-up-equal-of-len-of-cons-nest-and-number
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (and (eq 'equal fn) ;(equal (len <cons-nest>) <n>)
             (eql 2 (len args))
             (call-of 'len (first args))
             (eql 1 (len (fargs (first args))))
             (or (natp (second args))
                 (and (myquotep (second args)) ;TODO: stronger version of quotep that checks for at least 1 arg
                      (equal 1 (len (fargs (second args))))
                      (natp (unquote (second args))))))
        (let* ((n (second args))
               (n (if (natp n) n (unquote n))))
          (simplify-equality-of-len-of-cons-nest-and-number (farg1 (first args)) n))
      (cons fn args))))



;;TTODO: Add support for lambdas!
;; Doesn't work because it doesn't replace variables (improve def-untranslated-term-fold to take an argument specifying what to do to variables?)
;; (def-untranslated-term-fold replace
;;   (let* (;; (fn (if (consp fn)
;;          ;;         ;;if it's a lambda application, recur on the body:
;;          ;;         (let* ((lambda-formals (ulambda-formals fn))
;;          ;;                (declares (ulambda-declares fn))
;;          ;;                (lambda-body (ulambda-body fn))
;;          ;;                (lambda-body (:recur lambda-body alist))
;;          ;;                )
;;          ;;           `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
;;          ;;       fn))
;;          (term `(,fn ,@args)))
;;     (if (assoc-equal term alist)
;;         (cdr (assoc-equal term alist))
;;       term))
;;   :extra-args (alist)
;;   :extra-guards ((alistp alist) (untranslated-term-listp (strip-cdrs alist))))

;TODO: Does this handle lambdas right? See what's done with lambdas in replace-params-in-calls-in-term
(mutual-recursion
 (defun replace-in-untranslated-term (term alist)
   (declare (xargs :guard (and (untranslated-termp term)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))
                   :verify-guards nil
                   :hints (("Goal" :do-not-induct t))
                   :ruler-extenders :all))
   (if (assoc-equal term alist)
       (cdr (assoc-equal term alist))
     (if (atom term)
         term
       (if (fquotep term)
           term
         (let* ((fn (ffn-symb term)))
           ;; todo: think about this:
           (if (member-eq fn '(let let*))
               (let ((bindings (let-bindings term))
                     (declares (let-declares term))
                     (body (let-body term)))
                 `(,fn ,(make-let-bindings (let-binding-vars bindings)
                                           (replace-in-untranslated-term-list (let-binding-terms bindings) alist))
                       ,@declares
                       ,(replace-in-untranslated-term body alist)))
             ;; todo: think about this:
             (if (eq fn 'b*)
                 (let* ((bindings (farg1 term))
                        (result-forms (rest (fargs term)))
                        (terms (extract-terms-from-b*-bindings bindings))
                        (new-terms (replace-in-untranslated-term-list terms alist))
                        (new-bindings (recreate-b*-bindings bindings new-terms)))
                   `(b* ,new-bindings
                      ,@(replace-in-untranslated-term-list result-forms alist)))
               (if (eq 'cond fn)
                   (let* ((clauses (fargs term))
                          (terms (extract-terms-from-cond-clauses clauses))
                          (new-terms (replace-in-untranslated-term-list terms alist)))
                     `(cond ,@(recreate-cond-clauses clauses new-terms)))
                 (if (eq fn 'case) ;; (case <expr> ...pairs...)
                     (let* ((expr (farg1 term))
                            (pairs (cdr (fargs term)))
                            (vals-to-match (strip-cars pairs))
                            (vals-to-return (strip-cadrs pairs)))
                       `(case ,(replace-in-untranslated-term expr alist)
                          ,@(make-doublets vals-to-match
                                           (replace-in-untranslated-term-list vals-to-return alist))))
                   (if (eq fn 'case-match) ; (case-match sym ...cases...)
                       (b* ((sym (farg1 term)) ; must be a symbol
                            (new-sym (replace-in-untranslated-term sym alist))
                            ((when (not (and (symbolp new-sym)
                                             (untranslated-termp new-sym)))) ; todo: could let-bind a new var, for use in the case-match?
                             (er hard? 'replace-in-untranslated-term "Attempt to create a case-match whose first argument is ~x0, which is not a legal symbol." new-sym))
                            (cases (rest (fargs term)))
                            (terms-from-cases (extract-terms-from-case-match-cases cases))
                            (new-terms-from-cases (replace-in-untranslated-term-list terms-from-cases alist))
                            (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                         `(case-match ,new-sym ,@new-cases))
                     (let* ((args (fargs term))
                            (args (replace-in-untranslated-term-list args alist)))
                       ;;todo: handle lambdas
                       (let* ((term (cons fn args)))
                         term))))))))))))

 ;; (defun replace-in-var-untranslated-term-pairs
 ;;   (pairs alist)
 ;;   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
 ;;                               (alistp alist)
 ;;                               (untranslated-term-listp (strip-cdrs alist)))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;       (let* ((pair (first pairs))
 ;;              (var (first pair))
 ;;              (term (second pair)))
 ;;             (cons (list var (replace-in-untranslated-term term alist))
 ;;                   (replace-in-var-untranslated-term-pairs (rest pairs)
 ;;                                                           alist)))))
 (defun replace-in-untranslated-term-list
   (terms alist)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp terms)
       nil
       (cons (replace-in-untranslated-term (first terms)
                                           alist)
             (replace-in-untranslated-term-list (rest terms)
                                                alist)))))

(make-flag replace-in-untranslated-term)

(defthm len-of-replace-in-untranslated-term-list
  (equal (len (replace-in-untranslated-term-list terms alist))
         (len terms))
  :hints (("Goal" :in-theory (enable (:i len))
           :induct (len terms))))

(defthm consp-of-replace-in-untranslated-term-list
  (equal (consp (replace-in-untranslated-term-list terms alist))
         (consp terms))
  :hints (("Goal" :expand (replace-in-untranslated-term-list terms alist))))

(defthm-flag-replace-in-untranslated-term
  (defthm untranslated-termp-of-replace-in-untranslated-term
    (implies (and (untranslated-termp term)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-termp (replace-in-untranslated-term term alist)))
    :flag replace-in-untranslated-term)
  ;; (defthm var-untranslated-term-pairsp-of-replace-in-var-untranslated-term-pairs
  ;;   (implies (and (var-untranslated-term-pairsp pairs)
  ;;                 (alistp alist)
  ;;                 (untranslated-term-listp (strip-cdrs alist)))
  ;;            (var-untranslated-term-pairsp (replace-in-var-untranslated-term-pairs pairs alist)))
  ;;   :flag replace-in-var-untranslated-term-pairs)
  (defthm untranslated-term-listp-ofreplace-in-untranslated-term-list
    (implies (and (untranslated-term-listp terms)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-term-listp (replace-in-untranslated-term-list terms alist)))
    :flag replace-in-untranslated-term-list)
  :hints (("Goal" :in-theory (enable untranslated-lambda-exprp)
           :expand ((replace-in-untranslated-term term alist)))))

(VERIFY-GUARDS REPLACE-IN-UNTRANSLATED-TERM
  :HINTS (("Goal" :IN-THEORY (E/D (UNTRANSLATED-LAMBDA-EXPRP CONSP-WHEN-LEN-KNOWN)
                                  (UNTRANSLATED-TERMP UNTRANSLATED-TERM-LISTP
                                                      UNTRANSLATED-TERM-LISTP-OFREPLACE-IN-UNTRANSLATED-TERM-LIST))
           :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
           :DO-NOT-INDUCT T
           :USE ((:INSTANCE UNTRANSLATED-TERM-LISTP-OFREPLACE-IN-UNTRANSLATED-TERM-LIST
                            (TERMS (CDR TERM))))
           :EXPAND ((UNTRANSLATED-TERM-LISTP (REPLACE-IN-UNTRANSLATED-TERM-LIST (CDR TERM)
                                                                                ALIST))
                    (UNTRANSLATED-TERMP TERM)
                    (UNTRANSLATED-TERMP (CAR (REPLACE-IN-UNTRANSLATED-TERM-LIST (CDR TERM)
                                                                                ALIST))))))
  :OTF-FLG T)
;; test (TODO: Make unranslated-terms-tests and put this there using deftest):
;; (equal (replace-in-untranslated-term '(foo (bar 3)) (acons '(bar 3) '7 nil))
;;        '(foo 7))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only have to worry about the !v case.
(defun var-refs-in-case-match-pattern (pat)
  (declare (xargs :guard t))
  (if (symbolp pat)
      (and (> (length (symbol-name pat)) 0)
           (eql #\! (char (symbol-name pat) 0))
           (list (intern-in-package-of-symbol
                  (subseq (symbol-name pat)
                          1 (length (symbol-name pat)))
                  pat)))
    (and (consp pat)
         (append (var-refs-in-case-match-pattern (car pat)) (var-refs-in-case-match-pattern (cdr pat))))))

(defthm symbol-listp-of-var-refs-in-case-match-pattern
  (symbol-listp (var-refs-in-case-match-pattern pat)))

(defun var-refs-in-case-match-patterns (pats)
  (declare (xargs :guard t)) ; try (true-listp pats)
  (if (not (consp pats))
      nil
    (union-eq (var-refs-in-case-match-pattern (first pats))
              (var-refs-in-case-match-patterns (rest pats)))))

(defthm symbol-listp-of-var-refs-in-case-match-patterns
  (symbol-listp (var-refs-in-case-match-patterns pats)))

;; ;; todo: eventually drop.  also, use a named accessor instead of strip-cadrs
;; (defthm untranslated-term-listp-of-strip-cadrs-when-var-untranslated-term-pairsp
;;   (implies (var-untranslated-term-pairsp pairs)
;;            (untranslated-term-listp (strip-cadrs pairs))))

;; (defthm all->=-len-when-var-untranslated-term-pairsp-cheap
;;   (implies (var-untranslated-term-pairsp pairs)
;;            (all->=-len pairs 2))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0))))

;move up
(defthm all->=-len-of-let-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (all->=-len (let-bindings term) 2))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable let-bindings))))

;; (defthm alistp-when-var-untranslated-term-pairsp-cheap
;;   (implies (var-untranslated-term-pairsp pairs)
;;            (alistp pairs))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0))))

;move up
(defthm alistp-of-let-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (alistp (let-bindings term)))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable let-bindings))))

(defun var-untranslated-term-pairsp (pairs)
  (declare (xargs :guard t :measure (acl2-count pairs)))
  (if (atom pairs)
      (eq nil pairs)
    (let ((pair (first pairs)))
      (and (true-listp pair)
           (eql 2 (len pair))
           (untranslated-variablep (first pair))
           (untranslated-termp (second pair))
           (var-untranslated-term-pairsp (rest pairs))))))

;todo: nicer way? drop?
(defthm var-untranslated-term-pairsp-when-LEGAL-LET-BINDINGSP-AUX
  (implies (and (LEGAL-LET-BINDINGSP-AUX bindings)
                (UNTRANSLATED-TERM-LISTP (LET-BINDING-TERMS bindings)))
           (var-untranslated-term-pairsp bindings ;(let-bindings term)
                                         ))
  :hints (("Goal" :in-theory (enable var-untranslated-term-pairsp LEGAL-LET-BINDINGSP-aux LET-BINDING-TERMS))))

;todo: nicer way? drop?
(defthm var-untranslated-term-pairsp-of-cadr
  (implies (and (UNTRANSLATED-TERMP TERM)
                (member-EQUAL (CAR TERM) '(let LET*)))
           (var-untranslated-term-pairsp (cadr term) ;(let-bindings term)
                                         ))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable UNTRANSLATED-TERMP LET-BINDING-TERMS LEGAL-LET-BINDINGSP))))

(defthm untranslated-term-listp-of-let-binding-terms
  (implies (var-untranslated-term-pairsp bindings)
           (untranslated-term-listp (let-binding-terms bindings)))
  :hints (("Goal" :in-theory (enable let-binding-terms))))

;; ;; todo: deprecate this.  to do this right, we need the world so we can
;; ;; translate calls of user macros.
;; (mutual-recursion
;;  ;;Return a list of all variables in TERM.
;;  (defun free-vars-in-untranslated-term (term)
;;    (declare (xargs :guard (untranslated-termp term)
;;                    :verify-guards nil ;done below
;;                    ))
;;    (if (atom term)
;;        (if (untranslated-variablep term)
;;            (list term)
;;          ;; must be an unquoted constant:
;;          nil)
;;      (if (fquotep term)
;;          nil
;;        ;;function call or lambda
;;        (let* ((fn (ffn-symb term)))
;;          (if (eq fn 'let) ; (let <bindings> ...declares... <body>)
;;              (let* ((bindings (let-bindings term))
;;                     ;; (declares (let-declares term))
;;                     (body (let-body term))
;;                     (binding-vars (let-binding-vars bindings))
;;                     (binding-terms (let-binding-terms bindings)))
;;                (union-eq (free-vars-in-untranslated-term-list binding-terms)
;;                          (set-difference-eq (free-vars-in-untranslated-term body)
;;                                             binding-vars)))
;;            (if (eq fn 'let*) ; (let* <bindings> ...declares... <body>)
;;                (let* ((bindings (let-bindings term))
;;                       ;; (declares (let-declares term))
;;                       (body (let-body term)))
;;                  (mv-let (free-vars bound-vars)
;;                    (free-and-bound-vars-in-let*-bindings bindings nil nil)
;;                    (union-eq free-vars
;;                              (set-difference-eq (free-vars-in-untranslated-term body)
;;                                                 bound-vars))))
;;              (if (eq fn 'b*)
;;                  (let ((bindings (farg1 term))
;;                        (result-forms (rest (fargs term))))
;;                    ;; Fixme: See what we do for let*
;;                    (union-eq (free-vars-in-untranslated-term-list (extract-terms-from-b*-bindings bindings))
;;                              (free-vars-in-untranslated-term-list result-forms)))
;;                (if (eq 'cond fn) ; (cond ...clauses...)
;;                    (let* ((clauses (fargs term))
;;                           (terms (extract-terms-from-cond-clauses clauses)))
;;                      (free-vars-in-untranslated-term-list terms))
;;                  (if (eq fn 'case) ;; (case <expr> ...pairs...)
;;                      (let* ((expr (farg1 term))
;;                             (pairs (cdr (fargs term)))
;;                             ;; (vals-to-match (strip-cars pairs))
;;                             (vals-to-return (strip-cadrs pairs)))
;;                        (union-eq (free-vars-in-untranslated-term expr)
;;                                  (free-vars-in-untranslated-term-list vals-to-return)))
;;                    (if (eq fn 'case-match) ; (case-match sym ...cases...) ;; TODO: add vars only in pattern
;;                        (let* ((sym (farg1 term)) ; must be a symbol
;;                               (cases (rest (fargs term)))
;;                               (terms-from-cases (extract-terms-from-case-match-cases cases)))
;;                          ;; Fixme: See what we do for let*
;;                          (union-eq (if (untranslated-variablep sym)
;;                                        (list sym)
;;                                      nil)
;;                                    (union-eq (free-vars-in-untranslated-term-list terms-from-cases)
;;                                              (var-refs-in-case-match-patterns (strip-cars cases)))))
;;                      (let ((fn-res (if (consp fn)
;;                                        ;;if it's a lambda application, examine the body:
;;                                        (let ((lambda-body (ulambda-body fn)))
;;                                          (free-vars-in-untranslated-term lambda-body))
;;                                      ;;if it's not a lambda:
;;                                      nil)))
;;                        (union-eq fn-res (free-vars-in-untranslated-term-list (fargs term))))))))))))))

;;  ;; Returns (mv free-vars bound-vars).  The terms that appear in the PAIRS are
;;  ;; untranslated, since they came from a LET*.
;;  (defun free-and-bound-vars-in-let*-bindings (pairs free-vars-acc bound-vars-acc)
;;    (declare (xargs :guard (and (var-untranslated-term-pairsp pairs) ;todo: more specific name
;;                                (symbol-listp free-vars-acc)
;;                                (symbol-listp bound-vars-acc))))
;;    (if (endp pairs)
;;        (mv free-vars-acc bound-vars-acc)
;;      (let* ((pair (first pairs)) ; (<var> <term>)
;;             (var (first pair))
;;             (term (second pair))
;;             (term-vars (free-vars-in-untranslated-term term)))
;;        (free-and-bound-vars-in-let*-bindings (rest pairs)
;;                                              (union-eq (set-difference-eq term-vars bound-vars-acc) free-vars-acc)
;;                                              (add-to-set-eq var bound-vars-acc)))))

;;  ;; (defun get-vars-in-pat-untranslated-term-pairs (pairs
;;  ;;                                                 case-match-p ; todo: drop
;;  ;;                                                 )
;;  ;;   (declare (xargs :guard (pat-untranslated-term-pairsp pairs))
;;  ;;            (ignorable case-match-p))
;;  ;;   (if (endp pairs)
;;  ;;       nil
;;  ;;     (let* ((pair (first pairs))
;;  ;;            (pat (first pair))
;;  ;;            (term2 (car (last pair))))
;;  ;;       (union-eq (free-vars-in-untranslated-term term2)
;;  ;;                 (and case-match-p
;;  ;;                      (var-refs-in-case-match-pattern pat))
;;  ;;                 (get-vars-in-pat-untranslated-term-pairs (rest pairs) case-match-p)))))

;;  ;; Get all the free vars in the TERMS.
;;  (defun free-vars-in-untranslated-term-list (terms)
;;    (declare (xargs :guard (untranslated-term-listp terms)))
;;    (if (endp terms)
;;        nil
;;      (union-eq (free-vars-in-untranslated-term (first terms))
;;                (free-vars-in-untranslated-term-list (rest terms))))))

;; (make-flag flag-free-vars-in-untranslated-term free-vars-in-untranslated-term)

;; (defthm-flag-free-vars-in-untranslated-term
;;   (defthm symbol-listp-of-free-vars-in-untranslated-term
;;     (implies (untranslated-termp term)
;;              (symbol-listp (free-vars-in-untranslated-term term)))
;;     :flag free-vars-in-untranslated-term)
;;   ;;rename
;;   (defthm symbol-listp-of-free-and-bound-vars-in-let*-bindings
;;     (implies (and (var-untranslated-term-pairsp pairs)
;;                   (symbol-listp free-vars-acc)
;;                   (symbol-listp bound-vars-acc))
;;              (and (symbol-listp (mv-nth 0 (free-and-bound-vars-in-let*-bindings pairs free-vars-acc bound-vars-acc)))
;;                   (symbol-listp (mv-nth 1 (free-and-bound-vars-in-let*-bindings pairs free-vars-acc bound-vars-acc)))))
;;     :flag free-and-bound-vars-in-let*-bindings)
;;   ;; (defthm symbol-listp-of-get-vars-in-pat-untranslated-term-pairs
;;   ;;   (implies (pat-untranslated-term-pairsp pairs)
;;   ;;            (symbol-listp (get-vars-in-pat-untranslated-term-pairs pairs case-match-p)))
;;   ;;   :flag get-vars-in-pat-untranslated-term-pairs)
;;   (defthm symbol-listp-of-free-vars-in-untranslated-term-list
;;     (implies (untranslated-term-listp terms)
;;              (symbol-listp (free-vars-in-untranslated-term-list terms)))
;;     :flag free-vars-in-untranslated-term-list))

;; (defthm-flag-free-vars-in-untranslated-term
;;   (defthm true-listp-of-free-vars-in-untranslated-term
;;     (implies (untranslated-termp term)
;;              (true-listp (free-vars-in-untranslated-term term)))
;;     :flag free-vars-in-untranslated-term)
;;   ;; rename
;;   (defthm true-listp-of-free-and-bound-vars-in-let*-bindings
;;     (implies (and (var-untranslated-term-pairsp pairs)
;;                   (true-listp free-vars-acc)
;;                   (true-listp bound-vars-acc))
;;              (and (true-listp (mv-nth 0 (free-and-bound-vars-in-let*-bindings pairs free-vars-acc bound-vars-acc)))
;;                   (true-listp (mv-nth 1 (free-and-bound-vars-in-let*-bindings pairs free-vars-acc bound-vars-acc)))))
;;     :flag free-and-bound-vars-in-let*-bindings)
;;   ;; (defthm true-listp-of-free-vars-in-untranslated-term-pairs
;;   ;;   (implies (untranslated-term-pairsp pairs)
;;   ;;            (true-listp (free-vars-in-untranslated-term-pairs pairs)))
;;   ;;   :flag free-vars-in-untranslated-term-pairs)
;;   ;; (defthm true-listp-of-get-vars-in-pat-untranslated-term-pairs
;;   ;;   (implies (pat-untranslated-term-pairsp pairs)
;;   ;;            (true-listp (get-vars-in-pat-untranslated-term-pairs pairs case-match-p)))
;;   ;;   :flag get-vars-in-pat-untranslated-term-pairs)
;;   (defthm true-listp-of-free-vars-in-untranslated-term-list
;;     (implies (untranslated-term-listp terms)
;;              (true-listp (free-vars-in-untranslated-term-list terms)))
;;     :flag free-vars-in-untranslated-term-list))

;; (verify-guards free-vars-in-untranslated-term)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; Get all calls of FN in TERM
;;;

;; Note: This does not handle lets, so vars appearing the the calls returned by
;; this function may not correspond to the free vars in TERM.

(mutual-recursion
 ;; Return a list of all calls in TERM of any of the FNS
 (defun get-calls-in-untranslated-term (term fns)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-listp fns))
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       nil
     (if (fquotep term)
         nil
       ;;function call or lambda
       (let* ((this-fn (ffn-symb term)))
         (if (member-eq this-fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (union-equal (get-calls-in-var-untranslated-term-pairs (farg1 term) fns)
                          (get-calls-in-untranslated-term (car (last (fargs term))) fns))
           (if (eq this-fn 'b*)
               (let ((bindings (farg1 term))
                     (result-forms (rest (fargs term))))
                 (union-equal (get-calls-in-untranslated-term-list (extract-terms-from-b*-bindings bindings) fns)
                              (get-calls-in-untranslated-term-list result-forms fns)))
             (if (eq 'cond this-fn) ; (cond ...clauses...)
                 (let* ((clauses (fargs term))
                        (terms (extract-terms-from-cond-clauses clauses)))
                   (get-calls-in-untranslated-term-list terms fns))
               (if (eq this-fn 'case)
                   (let* ((expr (farg1 term))
                          (pairs (cdr (fargs term)))
                          ;; (vals-to-match (strip-cars pairs))
                          (vals-to-return (strip-cadrs pairs)))
                     (union-equal (get-calls-in-untranslated-term expr fns)
                                  (get-calls-in-untranslated-term-list vals-to-return fns)))
                 (if (eq this-fn 'case-match) ; (case-match sym ...cases...)
                     (let* ( ;; (sym (farg1 term)) ; no called fns since it's a symbol
                            (cases (rest (fargs term)))
                            (terms-from-cases (extract-terms-from-case-match-cases cases))
                            )
                       (get-calls-in-untranslated-term-list terms-from-cases fns) ; todo: do we want fns from the patterns?  I think not.
                       )
                   (let ((fn-res (if (consp this-fn)
                                     ;;if it's a lambda application, examine the body:
                                     (get-calls-in-untranslated-term (ulambda-body this-fn) fns)
                                   ;;if it's not a lambda:
                                   nil))
                         (res (if (member-eq this-fn fns)
                                  (list term)
                                nil)))
                     (union-equal fn-res
                                  (union-equal res
                                               (get-calls-in-untranslated-term-list (fargs term) fns)))))))))))))

 (defun get-calls-in-var-untranslated-term-pairs (pairs fns)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (symbol-listp fns))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            ;;(var (first pair))
            (term (second pair)))
       (union-equal (get-calls-in-untranslated-term term fns)
                    (get-calls-in-var-untranslated-term-pairs (rest pairs) fns)))))

 ;; (defun get-calls-in-cadrs-of-untranslated-term-pairs (pairs fns)
 ;;   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
 ;;                               (symbol-listp fns))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            ;;(term1 (first pair))
 ;;            (term2 (second pair)))
 ;;       (union-equal (get-calls-in-untranslated-term term2 fns)
 ;;                    (get-calls-in-cadrs-of-untranslated-term-pairs (rest pairs) fns)))))

 ;; (defun get-calls-in-untranslated-term-pairs (pairs fns)
 ;;   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
 ;;                               (symbol-listp fns))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (term1 (first pair))
 ;;            (term2 (second pair)))
 ;;       (union-equal (union-equal (get-calls-in-untranslated-term term1 fns)
 ;;                                 (get-calls-in-untranslated-term term2 fns))
 ;;                    (get-calls-in-untranslated-term-pairs (rest pairs) fns)))))

 ;; (defun get-calls-in-pat-untranslated-term-pairs (pairs fns)
 ;;   (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
 ;;                               (symbol-listp fns))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (term2 (car (last pair))))
 ;;       (union-equal (get-calls-in-untranslated-term term2 fns)
 ;;                    (get-calls-in-pat-untranslated-term-pairs (rest pairs) fns)))))

 ;; Get all calls of any of the FNS in the TERMS.
 (defun get-calls-in-untranslated-term-list (terms fns)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (symbol-listp fns))))
   (if (endp terms)
       nil
     (union-equal (get-calls-in-untranslated-term (first terms) fns)
                  (get-calls-in-untranslated-term-list (rest terms) fns)))))

(make-flag get-calls-in-untranslated-term)

(defthm-flag-get-calls-in-untranslated-term
  (defthm true-listp-of-get-calls-in-untranslated-term
    (implies (untranslated-termp term)
             (true-listp (get-calls-in-untranslated-term term fns)))
    :flag get-calls-in-untranslated-term)
  (defthm true-listp-of-get-calls-in-var-untranslated-term-pairs
    (implies (var-untranslated-term-pairsp pairs)
             (true-listp (get-calls-in-var-untranslated-term-pairs pairs fns)))
    :flag get-calls-in-var-untranslated-term-pairs)
  ;; (defthm true-listp-of-get-calls-in-cadrs-of-untranslated-term-pairs
  ;;   (implies (untranslated-term-pairsp pairs)
  ;;            (true-listp (get-calls-in-cadrs-of-untranslated-term-pairs pairs fns)))
  ;;   :flag get-calls-in-cadrs-of-untranslated-term-pairs)
  ;; (defthm true-listp-of-get-calls-in-untranslated-term-pairs
  ;;   (implies (untranslated-term-pairsp pairs)
  ;;            (true-listp (get-calls-in-untranslated-term-pairs pairs fns)))
  ;;   :flag get-calls-in-untranslated-term-pairs)
  ;; (defthm true-listp-of-get-calls-in-pat-untranslated-term-pairs
  ;;   (implies (pat-untranslated-term-pairsp pairs)
  ;;            (true-listp (get-calls-in-pat-untranslated-term-pairs pairs fns)))
  ;;   :flag get-calls-in-pat-untranslated-term-pairs)
  (defthm true-listp-of-get-calls-in-untranslated-term-list
    (implies (untranslated-term-listp terms)
             (true-listp (get-calls-in-untranslated-term-list terms fns)))
    :flag get-calls-in-untranslated-term-list))

(verify-guards get-calls-in-untranslated-term
               :otf-flg t
               :hints (("Goal" :in-theory (enable true-listp-when-symbol-listp-rewrite-unlimited))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; sublis-var-untranslated-term
;;;

;; (defund ulet-body (term)
;;   (declare (xargs :guard (and (untranslated-termp term)
;;                               (call-of 'let term))))
;;   ;; skip over the bindings and all the declares
;;   (car (last (rest (fargs term)))))

;; (defund ulet-bindings (term)
;;   (declare (xargs :guard (and (untranslated-termp term)
;;                               (call-of 'let term))))
;;   ;; skip over the bindings and all the declares
;;   (farg1 term))

;; (defund ulet-declares (term)
;;   (declare (xargs :guard (and (untranslated-termp term)
;;                               (call-of 'let term))))
;;   ;; skip over the bindings get everything but the body
;;   (butlast (rest (fargs term)) 1))

;; (defthm <-of-acl2-count-of-ulet-body
;;   (implies (consp term)
;;            (< (acl2-count (ulet-body term))
;;               (acl2-count term)))
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable ulet-body))))

;; (defthm <-of-acl2-count-of-ulet-bindings
;;   (implies (consp term)
;;            (< (acl2-count (ulet-bindings term))
;;               (acl2-count term)))
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable ulet-bindings))))

(defund all-untranslated-variablep (vars)
;  (declare (xargs :guard t))
  (if (atom vars)
      t
    (and (untranslated-variablep (first vars))
         (all-untranslated-variablep (rest vars)))))

;; (defthm untranslated-termp-of-ulet-body
;;   (implies (and (untranslated-termp term)
;;                 (call-of 'let term))
;;            (untranslated-termp (ulet-body term)))
;;   :hints (("Goal" :expand (untranslated-termp term)
;;            :in-theory (enable ulet-body))))

(defthm var-untranslated-term-pairsp-of-make-doublets
  (implies (and (all-untranslated-variablep vars)
                (untranslated-term-listp terms))
           (var-untranslated-term-pairsp (make-doublets vars terms)))
  :hints (("Goal" :in-theory (enable make-doublets
                                     all-untranslated-variablep))))

(defthm untranslated-term-listp-of-strip-cadrs-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (untranslated-term-listp (strip-cadrs pairs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; (defthm untranslated-term-listp-of-strip-cadrs-of-ulet-bindings
;;   (implies (and (untranslated-termp term)
;;                 (call-of 'let term))
;;            (untranslated-term-listp (strip-cadrs (ulet-bindings term))))
;;   :hints (("Goal" :expand (untranslated-termp term)
;;            :in-theory (enable ulet-bindings))))

(defthm all-untranslated-variablep-of-strip-cars-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (all-untranslated-variablep (strip-cars pairs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable ALL-UNTRANSLATED-VARIABLEP))))

;; (defthm all-untranslated-variablep-of-strip-cars-of-ulet-bindings
;;   (implies (and (untranslated-termp term)
;;                 (call-of 'let term))
;;            (all-untranslated-variablep (strip-cars (ulet-bindings term))))
;;   :hints (("Goal" :expand (untranslated-termp term)
;;            :in-theory (enable ulet-bindings))))

(defthm symbol-alistp-when-var-untranslated-term-pairsp-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (symbol-alistp pairs))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

;; (defthm all->=-len-of-ulet-bindings
;;   (implies (and (untranslated-termp term)
;;                 (call-of 'let term))
;;            (all->=-len (ulet-bindings term) 2))
;;   :hints (("Goal" :expand (untranslated-termp term)
;;            :in-theory (enable ulet-bindings))))

;; (defthm alistp-of-ulet-bindings
;;   (implies (and (untranslated-termp term)
;;                 (call-of 'let term))
;;            (alistp (ulet-bindings term)))
;;   :hints (("Goal" :expand (untranslated-termp term)
;;            :in-theory (enable ulet-bindings))))

;; (defthm symbol-alistp-of-ulet-bindings
;;   (implies (and (untranslated-termp term)
;;                 (call-of 'let term))
;;            (symbol-alistp (ulet-bindings term)))
;;   :hints (("Goal" :expand (untranslated-termp term)
;;            :in-theory (enable ulet-bindings))))

(defthm untranslated-term-listp-of-strip-cdrs-of-remove-assocs-equal
  (implies (untranslated-term-listp (strip-cdrs alist))
           (untranslated-term-listp (strip-cdrs (remove-assocs-equal keys alist))))
  :hints (("Goal" :in-theory (enable remove-assocs-equal))))

(defthm symbol-alistp-of-remove-assocs-equal
  (implies (symbol-alistp alist)
           (symbol-alistp (remove-assocs-equal keys alist)))
  :hints (("Goal" :in-theory (enable remove-assocs-equal symbol-alistp))))

;; It is simpler to replace a variable than a larger term because lambdas are easier to handle.
;todo: deprecate this:
(mutual-recursion
 (defun sublis-var-untranslated-term (alist term)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))
                   :verify-guards nil
                   :measure (acl2-count term)
                   :hints (("Goal" :do-not-induct t))
                   :ruler-extenders :all))
   (if (untranslated-variablep term)
       (if (assoc-equal term alist)
           (cdr (assoc-equal term alist))
         term)
     (if (atom term)
         term
       (if (fquotep term)
           term
         (let* ((fn (ffn-symb term)))
           (if (eq fn 'let)
               ;; (let <bindings> ...declares... <body>)
               (b* ((bindings (let-bindings term))
                    (declares (let-declares term))
                    (body (let-body term))
                    (vars (let-binding-vars bindings))
                    (terms (let-binding-terms bindings))
                    ;; Apply the replacement to the terms to which the vars
                    ;; are bound (okay because all bindings happen
                    ;; simultaneously):
                    (new-terms (sublis-var-untranslated-term-list alist terms))
                    ;; Remove any bindings whose vars are shadowed by the let:
                    (alist-for-body (remove-assocs vars alist))
                    ;; (body-vars (free-vars-in-untranslated-term$ body wrld)) ; todo: requires the world
                    ;; FIXME, if there is overlap between 1) vars in the replacements for free vars in the body, and 2) the bound vars, then signal an error (for now)
                    (new-body (sublis-var-untranslated-term alist-for-body body)))
                 `(let ,(make-let-bindings vars new-terms) ,@declares ,new-body))
             (if (eq fn 'let*) ;fffixme
               (let* ((bindings (let-bindings term))
                      (declares (let-declares term))
                      (body (let-body term)))
                 `(let* ,(sublis-var-in-let*-bindings alist bindings)
                    ,@declares
                    ,(sublis-var-untranslated-term alist body)))
               (if (eq fn 'b*) ;fffixme
                   (let* ((bindings (farg1 term))
                          (result-forms (rest (fargs term)))
                          (terms (extract-terms-from-b*-bindings bindings))
                          (new-terms (sublis-var-untranslated-term-list alist terms))
                          (new-bindings (recreate-b*-bindings bindings new-terms)))
                     `(b* ,new-bindings
                        ,@(sublis-var-untranslated-term-list alist result-forms)))
                 (if (eq 'cond fn) ; (cond ...clauses...)
                     (let* ((clauses (fargs term))
                            (terms (extract-terms-from-cond-clauses clauses))
                            (new-terms (sublis-var-untranslated-term-list alist terms)))
                       `(cond ,@(recreate-cond-clauses clauses new-terms)))
                   (if (eq fn 'case) ;; (case <expr> ...pairs...)
                       (let* ((expr (farg1 term))
                              (pairs (cdr (fargs term)))
                              (vals-to-match (strip-cars pairs))
                              (vals-to-return (strip-cadrs pairs)))
                         `(case ,(sublis-var-untranslated-term alist expr)
                            ,@(make-doublets vals-to-match
                                             (sublis-var-untranslated-term-list alist vals-to-return))))
                     (if (eq fn 'case-match) ; (case-match sym ...cases...)
                         (b* ((sym (farg1 term)) ; must be a symbol
                              (new-sym (sublis-var-untranslated-term alist sym))
                              ((when (not (and (symbolp new-sym)
                                               (untranslated-termp new-sym)))) ; todo: could let-bind a new var, for use in the case-match?
                               (er hard? 'sublis-var-untranslated-term "Attempt to create a case-match whose first argument is ~x0, which is not a legal symbol." new-sym))
                              (cases (rest (fargs term)))
                              ;;(terms-from-cases (extract-terms-from-case-match-cases cases))
                              ;;(new-terms-from-cases (sublis-var-untranslated-term-list alist terms-from-cases))
                              ;;(new-cases (recreate-case-match-cases cases new-terms-from-cases))
                              (new-cases (sublis-var-case-match-cases alist cases)))
                           `(case-match ,new-sym ,@new-cases))
                       (let* ((args (fargs term))
                              (args (sublis-var-untranslated-term-list alist args)))
                         ;;todo: handle lambdas
                         (let* ((term (cons fn args)))
                           term)))))))))))))

 (defun sublis-var-in-let*-bindings (alist pairs)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (var (first pair))
            (term (second pair)))
       (cons (list var
                   (sublis-var-untranslated-term alist term))
             (sublis-var-in-let*-bindings alist
                                                     (rest pairs))))))

 ;; (defun sublis-var-untranslated-term-pairs (alist pairs)
 ;;   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
 ;;                               (symbol-alistp alist)
 ;;                               (untranslated-term-listp (strip-cdrs alist)))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (term1 (first pair))
 ;;            (term2 (second pair)))
 ;;       (cons (list (sublis-var-untranslated-term alist term1)
 ;;                   (sublis-var-untranslated-term alist term2))
 ;;             (sublis-var-untranslated-term-pairs alist (rest pairs))))))

 ;fixme: consider capture
 (defun sublis-var-case-match-cases (alist cases)
   (declare (xargs :guard (and (legal-case-match-casesp cases)
                               (untranslated-term-listp (extract-terms-from-case-match-cases cases))
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp cases)
       nil
     (let* ((case (first cases))
            (pattern (first case))
            (declares (butlast (rest case) 1)) ; may be empty
            (body (car (last case)))
            (alist-for-body (remove-assocs (vars-bound-in-case-match-pattern pattern) alist)))
       (cons `(,pattern
               ,@declares
               ,(sublis-var-untranslated-term alist-for-body body))
             (sublis-var-case-match-cases alist (rest cases))))))

 (defun sublis-var-untranslated-term-list
   (alist terms)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp terms)
       nil
     (cons (sublis-var-untranslated-term alist
                                         (first terms))
           (sublis-var-untranslated-term-list alist
                                              (rest terms))))))

(make-flag sublis-var-untranslated-term)

(defthm len-of-sublis-var-untranslated-term-list
  (equal (len (sublis-var-untranslated-term-list alist terms))
         (len terms))
  :hints (("goal" :in-theory (enable (:i len))
           :induct (len terms))))

(defthm consp-of-sublis-var-untranslated-term-list
  (equal (consp (sublis-var-untranslated-term-list alist terms))
         (consp terms))
  :hints (("goal" :expand (sublis-var-untranslated-term-list alist terms))))

(defthm untranslated-term-listp-of-cons
  (equal (untranslated-term-listp (cons term terms))
         (and (untranslated-termp term)
              (untranslated-term-listp terms)))
  :hints (("Goal" :in-theory (enable untranslated-term-listp))))

(defthm-flag-sublis-var-untranslated-term
  (defthm untranslated-termp-of-sublis-var-untranslated-term
    (implies (and (untranslated-termp term)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-termp (sublis-var-untranslated-term alist term)))
    :flag sublis-var-untranslated-term)
  (defthm var-untranslated-term-pairsp-of-sublis-var-in-let*-bindings
    (implies (and (var-untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (and (LEGAL-LET-BINDINGSP (sublis-var-in-let*-bindings alist pairs))
                  (var-untranslated-term-pairsp (sublis-var-in-let*-bindings alist pairs))))
    :flag sublis-var-in-let*-bindings)
  ;; (defthm untranslated-term-pairsp-of-sublis-var-untranslated-term-pairs
  ;;   (implies (and (untranslated-term-pairsp pairs)
  ;;                 (alistp alist)
  ;;                 (untranslated-term-listp (strip-cdrs alist)))
  ;;            (untranslated-term-pairsp (sublis-var-untranslated-term-pairs alist pairs)))
  ;;   :flag sublis-var-untranslated-term-pairs)
  (defthm untranslated-term-listp-of-sublis-var-case-match-cases
    (implies (and (legal-case-match-casesp cases)
                  (untranslated-term-listp (extract-terms-from-case-match-cases cases))
                  (alistp alist) ;(symbol-alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (and (legal-case-match-casesp (sublis-var-case-match-cases alist cases))
                  (untranslated-term-listp (extract-terms-from-case-match-cases (sublis-var-case-match-cases alist cases)))))
    :flag sublis-var-case-match-cases)
  (defthm untranslated-term-listp-of-sublis-var-untranslated-term-list
    (implies (and (untranslated-term-listp terms)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-term-listp (sublis-var-untranslated-term-list alist terms)))
    :flag sublis-var-untranslated-term-list)
  :hints (("goal" :in-theory (enable untranslated-lambda-exprp
                                     legal-case-match-casesp)
           :expand ((sublis-var-untranslated-term term alist)
                    (SUBLIS-VAR-CASE-MATCH-CASES ALIST CASES)))))

(local
 (defthm last-when-equal-of-len
   (implies (and (equal free (len x))
                 (syntaxp (quotep free)))
            (equal (last x)
                   (nthcdr (+ -1 free) x)))
   :hints (("Goal" :in-theory (enable last)))))

(verify-guards sublis-var-untranslated-term
  :hints (("goal" :in-theory (e/d (untranslated-lambda-exprp consp-when-len-known)
                                  (untranslated-termp untranslated-term-listp
                                                      untranslated-term-listp-of-sublis-var-untranslated-term-list))
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :use ((:instance untranslated-term-listp-of-sublis-var-untranslated-term-list
                            (terms (cdr term))))
           :expand ((untranslated-term-listp (sublis-var-untranslated-term-list alist
                                                                                (cdr term)))
                    (untranslated-termp term)
                    (untranslated-termp (car (sublis-var-untranslated-term-list alist
                                                                                (cdr term))))
                    (EXTRACT-TERMS-FROM-CASE-MATCH-CASES CASES)
                    (LEGAL-CASE-MATCH-CASESP CASES)
                    (NTHCDR 2 (CAR CASES))
                    (NTHCDR 1 (CDR (CAR CASES)))
                    (NTHCDR 1 (CAR CASES)))))
  :otf-flg t)

;; (defthm alist-when-untranslated-term-pairsp-cheap
;;   (implies (untranslated-term-pairsp x)
;;            (alistp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; (defthm all->=-len-when-untranslated-term-pairsp-cheap
;;   (implies (untranslated-term-pairsp x)
;;            (all->=-len x 2))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; (defthm untranslated-term-listp-of-strip-cadrs
;;   (implies (untranslated-term-pairsp x)
;;            (untranslated-term-listp (strip-cadrs x))))

;; ;todo: just say farg 2
;; (defthm
;;  (implies (untranslated-lambda-exprp x)
;;           (untranslated-termp (car (last (fargs x)))))
;;  :hints (("Goal" :expand ((untranslated-lambda-exprp x))
;;           :in-theory (enable untranslated-lambda-exprp untranslated-termp))))

(in-theory (disable consp-of-cdr-of-car-when-untranslated-termp
                    cdr-of-car-when-untranslated-termp
                    true-listp-of-car-when-untranslated-termp
                    consp-of-cddr-of-car-when-untranslated-termp
                    untranslated-term-listp-of-cdr-2)) ;bad rules
