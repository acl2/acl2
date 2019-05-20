; System Utilities -- Term Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "../symbols")
(include-book "../symbol-symbol-alists")
(include-book "term-function-recognizers")
(include-book "world-queries")

(local (include-book "all-vars-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-utilities
  :parents (system-utilities-non-built-in)
  :short "Utilities for @(see term)s.")

(define lambda-closedp ((lambd pseudo-lambdap))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Check if a lambda expression is closed,
          i.e. it has no free variables."
  (subsetp-eq (all-vars (lambda-body lambd))
              (lambda-formals lambd))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

(define apply-term ((fn pseudo-termfnp) (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= (len terms)
                (len (lambda-formals fn))))
  :returns (term "A @(tsee pseudo-termp).")
  :parents (term-utilities)
  :short "Apply a function symbol or a lambda expression
          to a list of <see topic='@(url pseudo-termp)'>pseudo-terms</see>,
          obtaining a pseudo-term."
  :long
  "<p>
   This utility is similar to @(tsee cons-term),
   but it performs a beta reduction when @('fn') is a lambda expression.
   </p>"
  (cond ((symbolp fn) (cons-term fn terms))
        (t (subcor-var (lambda-formals fn) terms (lambda-body fn))))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))

(defsection apply-term*
  :parents (term-utilities)
  :short "Apply a function symbol or a lambda expression
          to <see topic='@(url pseudo-termp)'>pseudo-terms</see>,
          obtaining a pseudo-term."
  :long
  "<p>
   This utility is similar to @(tsee cons-term*),
   but it performs a beta reduction when @('fn') is a lambda expressions.
   </p>
   @(def apply-term*)"
  (defmacro apply-term* (fn &rest terms)
    `(apply-term ,fn (list ,@terms))))

(define apply-unary-to-terms ((fn pseudo-termfnp) (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= 1 (len (lambda-formals fn))))
  :returns (applied-terms "A @(tsee pseudo-term-listp).")
  :parents (term-utilities)
  :short "Apply a function symbol or a unary lambda expression
          to each element of a list of terms,
          obtaining a list of corresponding terms."
  (apply-unary-to-terms-aux fn terms nil)
  :verify-guards nil

  :prepwork
  ((define apply-unary-to-terms-aux ((fn pseudo-termfnp)
                                     (terms pseudo-term-listp)
                                     (rev-result pseudo-term-listp))
     :guard (or (symbolp fn)
                (= 1 (len (lambda-formals fn))))
     :returns (final-result "A @(tsee pseudo-term-listp).")
     (cond ((endp terms) (reverse rev-result))
           (t (apply-unary-to-terms-aux fn
                                        (cdr terms)
                                        (cons (apply-term* fn (car terms))
                                              rev-result))))
     :verify-guards nil)))

(define apply-terms-same-args ((fns pseudo-termfnp) (args pseudo-term-listp))
  :returns (terms "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :parents (term-utilities)
  :short "Apply each function symbol or lambda expression of a list
          to the same list of pseudo-term arguments,
          obtaining a list of corresponding function applications."
  :long
  "<p>
   This utility lifts @(tsee apply-term)
   from a single function to a list of functions.
   </p>"
  (if (endp fns)
      nil
    (cons (apply-term (car fns) args)
          (apply-terms-same-args (cdr fns) args))))

(define fapply-term ((fn pseudo-termfnp) (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= (len terms)
                (len (lambda-formals fn))))
  :returns (term "A @(tsee pseudo-termp).")
  :parents (term-utilities)
  :short "Variant of @(tsee apply-term) that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>"
  (cond ((symbolp fn) (fcons-term fn terms))
        (t (fsubcor-var (lambda-formals fn) terms (lambda-body fn))))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))

(defsection fapply-term*
  :parents (term-utilities)
  :short "Variant of @(tsee apply-term*) that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>
   @(def fapply-term*)"
  (defmacro fapply-term* (fn &rest terms)
    `(fapply-term ,fn (list ,@terms))))

(define fapply-unary-to-terms ((fn pseudo-termfnp)
                               (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= 1 (len (lambda-formals fn))))
  :returns (applied-terms "A @(tsee pseudo-term-listp).")
  :parents (term-utilities)
  :short "Variant of @(tsee apply-unary-to-terms)
          that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>"
  (fapply-unary-to-terms-aux fn terms nil)
  :verify-guards nil

  :prepwork
  ((define fapply-unary-to-terms-aux ((fn pseudo-termfnp)
                                      (terms pseudo-term-listp)
                                      (rev-result pseudo-term-listp))
     :guard (or (symbolp fn)
                (= 1 (len (lambda-formals fn))))
     :returns (final-result "A @(tsee pseudo-term-listp).")
     (cond ((endp terms) (reverse rev-result))
           (t (fapply-unary-to-terms-aux fn
                                         (cdr terms)
                                         (cons (fapply-term* fn (car terms))
                                               rev-result))))
     :verify-guards nil)))

(define fapply-terms-same-args ((fns pseudo-termfnp) (args pseudo-term-listp))
  :returns (terms "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :parents (term-utilities)
  :short "Variant of @(tsee apply-terms-same-args)
          that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>"
  (if (endp fns)
      nil
    (cons (fapply-term (car fns) args)
          (fapply-terms-same-args (cdr fns) args))))

(defines fsublis-var
  :parents (term-utilities)
  :short "Variant of @(tsee sublis-var) that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>
   @(def fsublis-var)
   @(def fsublis-var-lst)"

  (define fsublis-var ((alist (and (symbol-alistp alist)
                                   (pseudo-term-listp (strip-cdrs alist))))
                       (term pseudo-termp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (cond ((variablep term) (b* ((pair (assoc-eq term alist)))
                              (cond (pair (cdr pair))
                                    (t term))))
          ((fquotep term) term)
          (t (b* ((fn (ffn-symb term))
                  (args (fsublis-var-lst alist (fargs term))))
               (fcons-term fn args)))))

  (define fsublis-var-lst ((alist (and (symbol-alistp alist)
                                       (pseudo-term-listp (strip-cdrs alist))))
                           (terms pseudo-term-listp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (cond ((endp terms) nil)
          (t (cons (fsublis-var alist (car terms))
                   (fsublis-var-lst alist (cdr terms)))))))

(defines fsublis-fn-rec
  :parents (term-utilities)
  :short "Variant of @('sublis-fn-rec') that performs no simplification."
  :long
  "<p>
   @('sublis-fn-rec') is in the ACL2 source code.
   </p>
   <p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>
   <p>
   The definition of this utility is identical to @('sublis-fn-rec'),
   except that @(tsee cons-term) and @(tsee sublis-var)
   are replaced by @(tsee fcons-term) and @(tsee fsublis-var).
   We also use @(tsee endp) instead of @(tsee null)
   in the exit test of @('fsublis-fn-rec-lst')
   so that termination can be proved and the function is in logic mode.
   </p>
   @(def fsublis-fn-rec)
   @(def fsublis-fn-rec-lst)"
  :verify-guards nil

  (define fsublis-fn-rec ((alist symbol-alistp)
                          (term pseudo-termp)
                          (bound-vars symbol-listp)
                          (allow-freevars-p booleanp))
    :returns (mv (vars "A @(tsee symbol-listp).")
                 (new-term "A @(tsee pseudo-termp)."))
    (cond
     ((variablep term) (mv nil term))
     ((fquotep term) (mv nil term))
     ((flambda-applicationp term)
      (let ((old-lambda-formals (lambda-formals (ffn-symb term))))
        (mv-let
          (erp new-lambda-body)
          (fsublis-fn-rec alist
                          (lambda-body (ffn-symb term))
                          (append old-lambda-formals bound-vars)
                          allow-freevars-p)
          (cond
           (erp (mv erp new-lambda-body))
           (t (mv-let
                (erp args)
                (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                    allow-freevars-p)
                (cond (erp (mv erp args))
                      (t (let* ((body-vars (all-vars new-lambda-body))
                                (extra-body-vars
                                 (set-difference-eq body-vars
                                                    old-lambda-formals)))
                           (mv nil
                               (fcons-term
                                (make-lambda
                                 (append old-lambda-formals extra-body-vars)
                                 new-lambda-body)
                                (append args extra-body-vars))))))))))))
     (t (let ((temp (assoc-eq (ffn-symb term) alist)))
          (cond
           (temp
            (cond ((symbolp (cdr temp))
                   (mv-let
                     (erp args)
                     (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                         allow-freevars-p)
                     (cond (erp (mv erp args))
                           (t (mv nil
                                  (fcons-term (cdr temp) args))))))
                  (t
                   (let ((bad (if allow-freevars-p
                                  (intersection-eq
                                   (set-difference-eq
                                    (all-vars (lambda-body (cdr temp)))
                                    (lambda-formals (cdr temp)))
                                   bound-vars)
                                (set-difference-eq
                                 (all-vars (lambda-body (cdr temp)))
                                 (lambda-formals (cdr temp))))))
                     (cond
                      (bad (mv bad term))
                      (t (mv-let
                           (erp args)
                           (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                               allow-freevars-p)
                           (cond (erp (mv erp args))
                                 (t (mv nil
                                        (fsublis-var
                                         (pairlis$ (lambda-formals (cdr temp))
                                                   args)
                                         (lambda-body (cdr temp)))))))))))))
           (t (mv-let (erp args)
                (fsublis-fn-rec-lst alist (fargs term) bound-vars
                                    allow-freevars-p)
                (cond (erp (mv erp args))
                      (t (mv nil
                             (fcons-term (ffn-symb term) args)))))))))))

  (define fsublis-fn-rec-lst ((alist symbol-alistp)
                              (terms pseudo-term-listp)
                              (bound-vars symbol-listp)
                              (allow-freevars-p booleanp))
    :returns (mv (vars "A @(tsee symbol-listp).")
                 (new-terms "A @(tsee pseudo-term-listp)."))
    (cond ((endp terms) (mv nil nil))
          (t (mv-let
               (erp term)
               (fsublis-fn-rec alist (car terms) bound-vars allow-freevars-p)
               (cond (erp (mv erp term))
                     (t (mv-let
                          (erp tail)
                          (fsublis-fn-rec-lst alist (cdr terms) bound-vars
                                              allow-freevars-p)
                          (cond (erp (mv erp tail))
                                (t (mv nil (cons term tail))))))))))))

(define fsublis-fn ((alist symbol-alistp)
                    (term pseudo-termp)
                    (bound-vars symbol-listp))
  :returns (mv (vars "A @(tsee symbol-listp).")
               (new-term "A @(tsee pseudo-termp)."))
  :verify-guards nil
  :parents (term-utilities)
  :short "Variant of @(tsee sublis-fn) that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>"
  (fsublis-fn-rec alist term bound-vars t))

(define fsublis-fn-simple ((alist symbol-symbol-alistp)
                           (term pseudo-termp))
  :returns (new-term "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (term-utilities)
  :short "Variant of @(tsee sublis-fn-simple) that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>"
  (mv-let (vars result)
    (fsublis-fn-rec alist term nil t)
    (assert$ (null vars)
             result)))

(define fsublis-fn-lst-simple ((alist symbol-symbol-alistp)
                               (terms pseudo-term-listp))
  :returns (new-terms "A @(tsee pseudo-term-listp).")
  :mode :program
  :parents (term-utilities)
  :short "Variant of @(tsee sublis-fn-lst-simple)
          that performs no simplification."
  :long
  "<p>
   The meaning of the starting @('f') in the name of this utility
   is analogous to @(tsee fcons-term) compared to @(tsee cons-term).
   </p>"
  (mv-let (vars result)
    (sublis-fn-rec-lst alist terms nil t)
    (assert$ (null vars)
             result)))

(defines all-lambdas
  :parents (term-utilities)
  :short "Lambda expressions in a term."
  :verify-guards nil ; done below

  (define all-lambdas ((term pseudo-termp) (ans pseudo-lambda-listp))
    :returns (final-ans pseudo-lambda-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn (ffn-symb term))
         (ans (if (flambdap fn)
                  (all-lambdas (lambda-body fn) (add-to-set-equal fn ans))
                ans)))
      (all-lambdas-lst (fargs term) ans)))

  (define all-lambdas-lst ((terms pseudo-term-listp) (ans pseudo-lambda-listp))
    :returns (final-ans pseudo-lambda-listp :hyp :guard)
    (if (endp terms)
        ans
      (all-lambdas-lst (cdr terms)
                       (all-lambdas (car terms) ans))))

  ///

  (verify-guards all-lambdas))

(defines all-program-ffn-symbs
  :parents (term-utilities)
  :short "Program-mode functions called by a term."
  :long
  "<p>
   The name of this function is consistent with
   the name of @('all-ffn-symbs') in the ACL2 source code.
   </p>
   @(def all-program-ffn-symbs)
   @(def all-program-ffn-symbs-lst)"
  :verify-guards nil

  (define all-program-ffn-symbs ((term pseudo-termp)
                                 (ans symbol-listp)
                                 (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn/lambda (ffn-symb term))
         (ans (if (flambdap fn/lambda)
                  (all-program-ffn-symbs (lambda-body fn/lambda) ans wrld)
                (if (logicp fn/lambda wrld)
                    ans
                  (add-to-set-eq fn/lambda ans)))))
      (all-program-ffn-symbs-lst (fargs term) ans wrld)))

  (define all-program-ffn-symbs-lst ((terms pseudo-term-listp)
                                     (ans symbol-listp)
                                     (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (endp terms)) ans)
         (ans (all-program-ffn-symbs (car terms) ans wrld)))
      (all-program-ffn-symbs-lst (cdr terms) ans wrld)))

  ///

  (verify-guards all-program-ffn-symbs))

(define lambda-logic-fnsp ((lambd pseudo-lambdap) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Check if a lambda expression is in logic mode,
          i.e. its body is in logic mode."
  :long
  "<p>
   The name of this function is consistent with
   the name of @('logic-fnsp') in the ACL2 source code.
   </p>"
  (logic-fnsp (lambda-body lambd) wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

(defines guard-verified-fnsp
  :parents (term-utilities)
  :short "Check if a term calls only guard-verified functions."
  :long
  "<p>
   Note that if @('term') includes @(tsee mbe),
   @('nil') is returned
   if any function inside the @(':logic') component of @(tsee mbe)
   is not guard-verified,
   even when @('term') could otherwise be fully guard-verified.
   </p>
   <p>
   The name of this function is consistent with
   the name of @('logic-fnsp') in the ACL2 source code.
   </p>
   @(def guard-verified-fnsp)
   @(def guard-verified-fnsp-lst)"

  (define guard-verified-fnsp ((term (termp term wrld))
                               (wrld plist-worldp-with-formals))
    :returns (yes/no booleanp)
    (or (variablep term)
        (fquotep term)
        (and (guard-verified-fnsp-lst (fargs term) wrld)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (guard-verified-p fn wrld)
                 (guard-verified-fnsp (lambda-body fn) wrld))))))

  (define guard-verified-fnsp-lst ((terms (term-listp terms wrld))
                                   (wrld plist-worldp-with-formals))
    :returns (yes/no booleanp)
    (or (endp terms)
        (and (guard-verified-fnsp (car terms) wrld)
             (guard-verified-fnsp-lst (cdr terms) wrld)))))

(define lambda-guard-verified-fnsp ((lambd (lambdap lambd wrld))
                                    (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Check if all the functions in a lambda expression
          are guard-verified."
  :long
  "<p>
   The name of this function is consistent with
   the name of @(tsee guard-verified-fnsp).
   </p>"
  (guard-verified-fnsp (lambda-body lambd) wrld)
  :guard-hints (("Goal" :in-theory (enable lambdap))))

(defines all-non-gv-ffn-symbs
  :parents (term-utilities)
  :short "Non-guard-verified functions called by a term."
  :long
  "<p>
   The name of this function is consistent with
   the name of @('all-ffn-symbs') in the ACL2 source code.
   </p>
   @(def all-non-gv-ffn-symbs)
   @(def all-non-gv-ffn-symbs-lst)"
  :verify-guards nil

  (define all-non-gv-ffn-symbs ((term pseudo-termp)
                                (ans symbol-listp)
                                (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn/lambda (ffn-symb term))
         (ans (if (flambdap fn/lambda)
                  (all-non-gv-ffn-symbs (lambda-body fn/lambda) ans wrld)
                (if (guard-verified-p fn/lambda wrld)
                    ans
                  (add-to-set-eq fn/lambda ans)))))
      (all-non-gv-ffn-symbs-lst (fargs term) ans wrld)))

  (define all-non-gv-ffn-symbs-lst ((terms pseudo-term-listp)
                                    (ans symbol-listp)
                                    (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (endp terms)) ans)
         (ans (all-non-gv-ffn-symbs (car terms) ans wrld)))
      (all-non-gv-ffn-symbs-lst (cdr terms) ans wrld))))

(define guard-verified-exec-fnsp ((term (termp term wrld))
                                  (wrld plist-worldp-with-formals))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (term-utilities)
  :short "Check if a term calls only guard-verified functions for execution."
  :long
  "<p>
   Check if all the functions that occur in the term, except possibly
   the ones in the @(':logic') subterms of @(tsee mbe)s
   and the ones called via @(tsee ec-call),
   are guard-verified.
   The purpose of this function is to check whether a term
   could be potentially guard-verified.
   </p>
   <p>
   The name of this function is consistent with
   the name of @(tsee guard-verified-fnsp).
   </p>
   <p>
   The @('all-fnnames-exec') built-in system utility
   returns all the function symbols except
   the ones in the @(':logic') subterms of @(tsee mbe)s
   and the ones called via @(tsee ec-call)
   (see the ACL2 source code).
   The @('collect-non-common-lisp-compliants') built-in system utility
   returns all the ones that are not guard-verified
   (see the ACL2 source code).
   </p>"
  (null (collect-non-common-lisp-compliants (all-fnnames-exec term) wrld)))

(define lambda-guard-verified-exec-fnsp ((lambd (lambdap lambd wrld))
                                         (wrld plist-worldp-with-formals))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (term-utilities)
  :short "Check if a lambda expression calls only guard-verified functions
          for execution."
  :long
  "<p>
   The name of this function is consistent with
   the name of @(tsee guard-verified-exec-fnsp).
   </p>"
  (guard-verified-exec-fnsp (lambda-body lambd) wrld))

(define all-non-gv-exec-ffn-symbs ((term pseudo-termp) (wrld plist-worldp))
  :returns (final-ans "A @(tsee symbol-listp).")
  :mode :program
  :parents (term-utilities)
  :short "Non-guard-verified functions called by a term for execution."
  "<p>
   These are all the non-guard-verified functions that occur in the term,
   except those that occur in the @(':logic') subterms of @(tsee mbe)s
   and those called via @(tsee ec-call).
   This is because, in order for a function to be guard-verified,
   the functions that occurs in such subterms do not have to be guard-verified.
   If this function returns @('nil'),
   the term could be potentially guard-verified.
   </p>
   <p>
   The name of this function is consistent with
   the name of @('all-ffn-symbs') in the ACL2 source code.
   </p>
   <p>
   The @('all-fnnames-exec') built-in system utility
   returns all the function symbols except
   the ones in the @(':logic') subterms of @(tsee mbe)s
   and the ones called via @(tsee ec-call)
   (see the ACL2 source code).
   The @('collect-non-common-lisp-compliants') built-in system utility
   returns all the ones that are not guard-verified
   (see the ACL2 source code).
   </p>"
  (collect-non-common-lisp-compliants (all-fnnames-exec term) wrld))

(defines all-pkg-names
  :parents (term-utilities)
  :short "Collect all the package names of all the symbols in a term."
  :long
  "@(def all-pkg-names)
   @(def all-pkg-names-lst)"
  :verify-guards nil ; done below

  (define all-pkg-names ((term pseudo-termp))
    :returns (pkg-names string-listp)
    (cond ((variablep term) (list (symbol-package-name term)))
          ((fquotep term) (if (symbolp (cadr term))
                              (list (symbol-package-name (cadr term)))
                            nil))
          ((symbolp (ffn-symb term))
           (add-to-set-equal (symbol-package-name (ffn-symb term))
                             (all-pkg-names-lst (fargs term))))
          (t (union-equal (remove-duplicates-equal
                           (symbol-package-name-lst
                            (lambda-formals (ffn-symb term))))
                          (union-equal (all-pkg-names (lambda-body
                                                       (ffn-symb term)))
                                       (all-pkg-names-lst (fargs term)))))))

  (define all-pkg-names-lst ((terms pseudo-term-listp))
    :returns (pkg-names string-listp)
    (cond ((endp terms) nil)
          (t (union-equal (all-pkg-names (car terms))
                          (all-pkg-names-lst (cdr terms))))))

  :prepwork
  ((local (include-book "std/typed-lists/string-listp" :dir :system))
   (local (include-book "kestrel/utilities/typed-lists/string-listp-theorems" :dir :system))
   (local (include-book "kestrel/utilities/lists/union-theorems" :dir :system)))

  ///

  (verify-guards all-pkg-names))

(define check-user-term (x (wrld plist-worldp))
  :returns (mv (term/message "A @(tsee pseudo-termp) or @(tsee msgp).")
               (stobjs-out "A @(tsee symbol-listp)."))
  :mode :program
  :parents (term-utilities)
  :short "Recognize <see topic='@(url term)'>untranslated</see> terms
          that are valid for evaluation."
  :long
  "<p>
   An untranslated @(see term) is a term as entered by the user.
   This function checks @('x') by attempting to translate it.
   If the translation succeeds, the translated term is returned,
   along with the @(tsee stobjs-out) list of the term (see below for details).
   Otherwise, a structured error message is returned (printable with @('~@')),
   along with @('nil') as @(tsee stobjs-out) list.
   These two possible outcomes can be distinguished by the fact that
   the former yields a <see topic='@(url pseudo-termp)'>pseudo-term</see>
   while the latter does not.
   </p>
   <p>
   The @(tsee stobjs-out) list of a term is the term analogous
   of the @(tsee stobjs-out) property of a function,
   namely a list of symbols that is like a &ldquo;mask&rdquo; for the result.
   A @('nil') in the list means that
   the corresponding result is a non-@(see stobj) value,
   while the name of a @(see stobj) in the list means that
   the corresponding result is the named @(see stobj).
   The list is a singleton, unless the term returns
   <see topic='@(url mv)'>multiple values</see>.
   </p>
   <p>
   The @(':stobjs-out') and @('((:stobjs-out . :stobjs-out))') arguments
   passed to @('translate1-cmp') as bindings
   mean that the term is checked to be valid for evaluation.
   This is stricter than checking the term to be valid for use in a theorem,
   and weaker than checking the term to be valid
   for use in the body of an executable function;
   these different checks are performed by passing different values
   to the second and third arguments of @('translate1-cmp')
   (see the ACL2 source code for details).
   However, for terms whose functions are all in logic mode,
   validity for evaluation and validity for executable function bodies
   should coincide.
   </p>
   <p>
   If @('translate1-cmp') is successful,
   it returns updated bindings that associate @(':stobjs-out')
   to the output stobjs of the term.
   </p>
   <p>
   The @(tsee check-user-term) function does not terminate
   if the translation expands an ill-behaved macro that does not terminate.
   </p>"
  (mv-let (ctx term/message bindings)
    (translate1-cmp x
                    :stobjs-out
                    '((:stobjs-out . :stobjs-out))
                    t
                    __function__
                    wrld
                    (default-state-vars nil))
    (declare (ignore ctx))
    (if (pseudo-termp term/message)
        (mv term/message
            (cdr (assoc :stobjs-out bindings)))
      (mv term/message nil))))

(define check-user-lambda (x (wrld plist-worldp))
  :returns (mv (lambd/message  "A @(tsee pseudo-termp) or @(tsee msgp).")
               (stobjs-out "A @(tsee symbol-listp)."))
  :mode :program
  :parents (term-utilities)
  :short "Recognize <see topic='@(url term)'>untranslated</see>
          lambda expressions that are valid for evaluation."
  :long
  "<p>
   An untranslated @(see lambda) expression is
   a lambda expression as entered by the user.
   This function checks whether @('x')is
   a true list of exactly three elements,
   whose first element is the symbol @('lambda'),
   whose second element is a list of legal variable symbols without duplicates,
   and whose third element is an untranslated term that is valid for evaluation.
   </p>
   <p>
   If the check succeeds, the translated lambda expression is returned,
   along with the @(tsee stobjs-out) list of the body of the lambda expression
   (see @(tsee check-user-term) for an explanation
   of the @(tsee stobjs-out) list of a term).
   Otherwise, a possibly structured error message is returned
   (printable with @('~@')),
   along with @('nil') as @(tsee stobjs-out) list.
   </p>
   <p>
   The @(tsee check-user-lambda) function does not terminate
   if @(tsee check-user-term) does not terminate.
   </p>"
  (b* (((unless (true-listp x))
        (mv (msg "~x0 is not a true list." x) nil))
       ((unless (= (len x) 3))
        (mv (msg "~x0 does not consist of exactly three elements." x) nil))
       ((unless (eq (first x) 'lambda))
        (mv (msg "~x0 does not start with LAMBDA." x) nil))
       ((unless (arglistp (second x)))
        (mv (msg "~x0 does not have valid formal parameters." x) nil))
       ((mv term/message stobjs-out) (check-user-term (third x) wrld))
       ((when (msgp term/message))
        (mv (msg "~x0 does not have a valid body.  ~@1" x term/message) nil)))
    (mv `(lambda ,(second x) ,term/message) stobjs-out)))

(define term-guard-obligation ((term pseudo-termp) state)
  :returns (obligation "A @(tsee pseudo-termp).")
  :mode :program
  :parents (term-utilities)
  :short "Formula expressing the guard obligation of a term."
  :long
  "<p>
   The case in which @('term') is a symbol is dealt with separately
   because @(tsee guard-obligation)
   interprets a symbol as a function or theorem name, not as a variable.
   </p>"
  (b* (((when (symbolp term)) *t*)
       ((mv erp val) (guard-obligation term nil nil t __function__ state))
       ((when erp)
        (raise "Error ~x0 when computing the guard obligation of ~x1."
               erp term))
       (obligation-clauses (cadr val))
       (obligation-formula (termify-clause-set obligation-clauses)))
    obligation-formula))

(define all-vars-in-untranslated-term (x (wrld plist-worldp))
  :returns (term "A @(tsee pseudo-termp).")
  :mode :program
  :parents (term-utilities)
  :short "The variables free in the given untranslated term."
  :long
  "<p>
   This function returns the variables of the given untranslated term.  They
   are returned in reverse order of print occurrence, for consistency with the
   function, @(tsee all-vars).
   </p>
   <p>
   The input is translated for reasoning, so restrictions for executability are
   not enforced.  There is also no restriction on the input being in
   @(':')@(tsee logic) mode.
   </p>"
  (let ((ctx 'all-vars-in-untranslated-term))
    (mv-let (erp term)
      (translate-cmp x
                     t ; stobjs-out
                     nil ; logic-modep (not required)
                     nil ; known-stobjs
                     ctx
                     wrld
                     (default-state-vars nil))
      (cond (erp (er hard erp "~@0" term))
            (t (all-vars term))))))
