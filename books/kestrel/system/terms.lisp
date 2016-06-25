; Term Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains utilities for ACL2 terms.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "kestrel/system/world-queries" :dir :system)

(local (set-default-parents term-utilities))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-utilities
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities related to <see topic='@(url term)'>terms</see>.")

(define all-fns ((term pseudo-termp))
  ;; :returns (fns symbol-listp)
  :short "Function symbols in a term."
  (all-ffn-symbs term nil))

(std::deflist legal-variable-listp (x)
  (legal-variablep x)
  :short
  "True iff @('x') is a @('nil')-terminated list of legal variable names."
  :long
  "<p>
  See @('legal-variablep') in the ACL2 source code.
  </p>"
  :true-listp t
  :elementp-of-nil nil)

(define pseudo-lambda-expr-p (x)
  :returns (yes/no booleanp)
  :short
  "True iff @('x') satisfies the conditions of lambda expressions
  in <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
  Check whether @('x') is
  a @('nil')-terminated list of exactly three elements,
  whose first element is the symbol @('lambda'),
  whose second element is a list of symbols, and
  whose third element is a pseudo-term.
  </p>"
  (and (true-listp x)
       (eql (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (pseudo-termp (third x))))

(define lambda-expr-closedp ((lambd pseudo-lambda-expr-p))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short
  "True iff the lambda expression is closed, i.e. it has no free variables."
  (subsetp (all-vars (lambda-body lambd))
           (lambda-formals lambd)))

(define pseudo-functionp (x)
  :returns (yes/no booleanp)
  :short
  "True iff @('x') satisfies the conditions of functions
  in <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
  Check whether @('x')is a symbol or a pseudo-lambda-expression.
  These are the possible values of the first element of
  a pseudo-term that is not a variable or a quoted constant
  (i.e. a pseudo-term that is a function application).
  </p>"
  (or (symbolp x)
      (pseudo-lambda-expr-p x)))

(define apply-term ((pfun pseudo-functionp) (terms pseudo-term-listp))
  :guard (or (symbolp pfun)
             (eql (len terms)
                  (len (lambda-formals pfun))))
  ;; :returns (term pseudo-termp)
  :guard-hints (("Goal" :in-theory (enable pseudo-functionp
                                           pseudo-lambda-expr-p)))
  :short
  "Apply pseudo-function to list of pseudo-terms, obtaining a pseudo-term."
  :long
  "<p>
  If the pseudo-function is a lambda expression,
  a beta reduction is performed.
  </p>"
  (cond ((symbolp pfun) (cons-term pfun terms))
        (t (subcor-var (lambda-formals pfun) terms (lambda-body pfun)))))

(defsection apply-term*
  :short
  "Apply pseudo-function to pseudo-terms, obtaining a pseudo-term."
  :long
  "<p>
  If the pseudo-function is a lambda expression,
  a beta reduction is performed.
  </p>
  @(def apply-term*)"
  (defmacro apply-term* (pfun &rest terms)
    `(apply-term ,pfun (list ,@terms))))

(define apply-unary-to-terms ((pfun pseudo-functionp) (terms pseudo-term-listp))
  ;; :returns (applied-terms pseudo-term-listp)
  :verify-guards nil
  :short
  "Apply @('pfun'), as a unary function, to each of @('terms'),
  obtaining a list of corresponding terms."
  (if (endp terms)
      nil
    (cons (apply-term* pfun (car terms))
          (apply-unary-to-terms pfun (cdr terms)))))

(defines term/terms-logicp
  :short "True iff term/terms is/are in logic mode."

  (define term-logicp ((term pseudo-termp) (w plist-worldp))
    :returns (yes/no booleanp)
    :parents (term/terms-logicp)
    :short
    "True iff the term is in logic mode,
    i.e. all its functions are in logic mode."
    (or (variablep term)
        (fquotep term)
        (and (terms-logicp (fargs term) w)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (logicp fn w)
                 (term-logicp (lambda-body fn) w))))))

  (define terms-logicp ((terms pseudo-term-listp) (w plist-worldp))
    :returns (yes/no booleanp)
    :parents (term/terms-logicp)
    :short "True iff all the terms are in logic mode."
    (or (endp terms)
        (and (term-logicp (car terms) w)
             (terms-logicp (cdr terms) w)))))

(define lambda-expr-logicp ((lambd pseudo-lambda-expr-p) (w plist-worldp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambda-expr-p)))
  :short
  "True iff the lambda expression is in logic mode,
  i.e. its body is in logic mode."
  (term-logicp (lambda-body lambd) w))

(defines term/terms-no-stobjs-p
  :prepwork ((program))
  :short "True iff term/terms has/have no stobjs."
  :flag nil

  (define term-no-stobjs-p ((term pseudo-termp) (w plist-worldp))
    :returns (yes/no booleanp)
    :parents (term/terms-no-stobjs-p)
    :short
    "True iff the term has no stobjs,
    i.e. all its functions have no stobjs."
    :long
    "<p>
    A term containing functions in @('*stobjs-out-invalid*')
    (on which @(tsee no-stobjs-p) would cause a guard violation),
    is regarded as having no stobjs,
    if all its other functions have no stobjs.
    </p>"
    (or (variablep term)
        (fquotep term)
        (and (terms-no-stobjs-p (fargs term) w)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (or (member fn *stobjs-out-invalid*)
                       (no-stobjs-p fn w))
                 (term-no-stobjs-p (lambda-body fn) w))))))

  (define terms-no-stobjs-p ((terms pseudo-term-listp) (w plist-worldp))
    :returns (yes/no booleanp)
    :parents (term/terms-no-stobjs-p)
    :short "True iff all the terms have no stobjs."
    (or (endp terms)
        (and (term-no-stobjs-p (car terms) w)
             (terms-no-stobjs-p (cdr terms) w)))))

(define lambda-expr-no-stobjs-p ((lambd pseudo-lambda-expr-p) (w plist-worldp))
  :returns (yes/no booleanp)
  :prepwork ((program))
  :short
  "True iff the lambda expression has no stobjs,
  i.e. its body has no stobjs."
  (term-no-stobjs-p (lambda-body lambd) w))

(defines term/terms-funs-guard-verified-p
  :short "True iff term/terms is/are guard-verified."
  :verify-guards nil

  (define term-funs-guard-verified-p ((term pseudo-termp) (w plist-worldp))
    :returns (yes/no booleanp)
    :parents (term/terms-funs-guard-verified-p)
    :short "True iff all the functions in the term are guard-verified."
    (or (variablep term)
        (fquotep term)
        (and (terms-funs-guard-verified-p (fargs term) w)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (guard-verified-p fn w)
                 (term-funs-guard-verified-p (lambda-body fn) w))))))

  (define terms-funs-guard-verified-p ((terms pseudo-term-listp)
                                       (w plist-worldp))
    :returns (yes/no booleanp)
    :parents (term/terms-funs-guard-verified-p)
    :short "True iff all the functions in the terms are guard-verified."
    (or (endp terms)
        (and (term-funs-guard-verified-p (car terms) w)
             (terms-funs-guard-verified-p (cdr terms) w)))))

(define lambda-expr-funs-guard-verified-p ((lambd pseudo-lambda-expr-p)
                                           (w plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short
  "True iff all the functions in the lambda expression is guard-verified."
  (term-funs-guard-verified-p (lambda-body lambd) w))

(define lambda-expr-p (x (w plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short
  "True iff @('x') is a valid translated lambda expression."
  :long
  "<p>
  Check whether @('x') is a @('nil')-terminated list of exactly three elements,
  whose first element is the symbol @('lambda'),
  whose second element is a list of legal variable symbols without duplicates,
  and whose third element is a valid translated term.
  </p>"
  (and (true-listp x)
       (eql (len x) 3)
       (eq (first x) 'lambda)
       (legal-variable-listp (second x))
       (no-duplicatesp (second x))
       (termp (third x) w)))

(define check-user-term (x (w plist-worldp))
  :returns (term/message (or (pseudo-termp term/message)
                             (msgp term/message)))
  :prepwork ((program))
  :short
  "Check whether @('x') is an untranslated term that is valid for evaluation."
  :long
  "<p>
  An untranslated term is a term as entered by the user.
  This function checks @('x') by attempting to translate it.
  If the translation succeeds, the translated term is returned.
  Otherwise, a structured error message is returned (printable with @('~@')).
  These two possible outcomes can be distinguished by the fact that
  the former is a pseudo-termp while the latter is not.
  </p>
  <p>
  The @(':stobjs-out') and @('((:stobjs-out . :stobjs-out))') arguments
  passed to @('translate1-cmp')
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
  This function does not terminate
  if the translation expands an ill-behaved macro that does not terminate.
  </p>"
  (mv-let (ctx term/message bindings)
    (translate1-cmp x
                    :stobjs-out
                    '((:stobjs-out . :stobjs-out))
                    t
                    __function__
                    w
                    (default-state-vars nil))
    (declare (ignore ctx bindings))
    term/message))

(define check-user-lambda-expr (x (w plist-worldp))
  :returns (lambd/message (or (pseudo-lambda-expr-p lambd/message)
                              (msgp lambd/message)))
  :prepwork ((program))
  :short
  "Check whether @('x') is
  an untranslated lambda expression that is valid for evaluation."
  :long
  "<p>
  An untranslated lambda expression is
  a lambda expression as entered by the user.
  This function checks whether @('x')is
  a @('nil')-terminated list of exactly three elements,
  whose first element is the symbol @('lambda'),
  whose second element is a list of legal variable symbols without duplicates,
  and whose third element is an untranslated term that is valid for evaluation.
  </p>
  <p>
  If the check succeeds, the translated lambda expression is returned.
  Otherwise, a possibly structured error message is returned
  (printable with @('~@')).
  </p>
  <p>
  This function does not terminate
  if @(tsee check-user-term) does not terminate.
  </p>"
  (b* (((unless (true-listp x))
        `("~x0 is not a NIL-terminated list." (#\0 . ,x)))
       ((unless (eql (len x) 3))
        `("~x0 does not consist of exactly three elements." (#\0 . ,x)))
       ((unless (eq (first x) 'lambda))
        `("~x0 does not start with LAMBDA." (#\0 . ,x)))
       ((unless (legal-variable-listp (second x)))
        `("~x0 does not have valid formal parameters." (#\0 . ,x)))
       ((unless (no-duplicatesp (second x)))
        `("~x0 has duplicate formal parameters." (#\0 . ,x)))
       (term/message (check-user-term (third x) w))
       ((when (msgp term/message)) term/message))
    `(lambda ,(second x) ,term/message)))

(define trans-macro ((mac (macro-namep mac w)) (w plist-worldp))
  :returns (term pseudo-termp)
  :prepwork ((program))
  :short "Translated term that a call to the macro translates to."
  :long
  "<p>
  This function translates a call to the macro
  that only includes the required arguments,
  returning the resulting translated term.
  </p>
  <p>
  Note that since the macro is in the ACL2 world
  (because of the @(tsee macro-namep) guard),
  the translation of the macro call should not fail.
  However, the translation may not terminate,
  as mentioned in @(tsee check-user-term).
  </p>
  <p>
  Note also that if the macro has optional arguments,
  its translation with non-default values for these arguments
  may yield different terms.
  </p>"
  (check-user-term (cons mac (macro-required-args mac w)) w))

(define term-guard-obligation ((term pseudo-termp) state)
  :returns (obligation pseudo-termp)
  :prepwork ((program))
  :short "Formula expressing the guard obligation of the term."
  :long
  "<p>
  The case in which @('term') is a symbol is dealt with separately
  because @(tsee guard-obligation)
  interprets a symbol as a function or theorem name, not as a variable.
  </p>"
  (b* (((when (symbolp term)) *t*)
       ((mv erp val) (guard-obligation term nil nil __function__ state))
       ((when erp)
        (raise "Error ~x0 when computing the guard obligation of ~x1."
               erp term))
       (obligation-clauses (cadr val))
       (obligation-formula (termify-clause-set obligation-clauses)))
    obligation-formula))
