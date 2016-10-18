; Term Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;
; Contributor: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains utilities for ACL2 terms.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "world-queries")

(local (include-book "all-vars-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-utilities
  :parents (kestrel-utilities system-utilities)
  :short "Utilities for @(see term)s.")

(define pseudo-lambdap (x)
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Recognize lambda expressions of
          <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
   Check whether @('x') is
   a @('nil')-terminated list of exactly three elements,
   whose first element is the symbol @('lambda'),
   whose second element is a list of symbols, and
   whose third element is a pseudo-term.
   </p>"
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (pseudo-termp (third x))))

(define pseudo-fn/lambda-p (x)
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Recognize symbols and
          lambda expressions of
          <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
   Check whether @('x') is a symbol or a
   <see topic='@(url pseudo-lambdap)'>pseudo-lambda-expression</see>.
   These are the possible values of the first element of
   a pseudo-term that is not a variable or a quoted constant
   (i.e. a pseudo-term that is a function application).
   </p>"
  (or (symbolp x)
      (pseudo-lambdap x)))

(define lambdap (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Recognize valid
          <see topic='@(url term)'>translated</see> lambda expression."
  :long
  "<p>
   Check whether @('x') is a @('nil')-terminated list of exactly three elements,
   whose first element is the symbol @('lambda'),
   whose second element is a list of legal variable symbols without duplicates,
   and whose third element is a valid translated term
   whose free variables are all among the ones in the second element.
   </p>"
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (arglistp (second x))
       (termp (third x) wrld)
       (subsetp-eq (all-vars (third x))
                   (second x))))

(define fn/lambda-p (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Recognize valid function symbols and
          <see topic='@(url term)'>translated</see> lambda expression."
  (or (function-namep x wrld)
      (lambdap x wrld)))

(define lambda-closedp ((lambd pseudo-lambdap))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Check if a lambda expression is closed,
          i.e. it has no free variables."
  (subsetp-eq (all-vars (lambda-body lambd))
              (lambda-formals lambd))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

(define apply-term ((fn pseudo-fn/lambda-p) (terms pseudo-term-listp))
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
   If a lambda expression is applied, a beta reduction is performed.
   </p>"
  (cond ((symbolp fn) (cons-term fn terms))
        (t (subcor-var (lambda-formals fn) terms (lambda-body fn))))
  :guard-hints (("Goal" :in-theory (enable pseudo-fn/lambda-p pseudo-lambdap))))

(defsection apply-term*
  :parents (term-utilities)
  :short "Apply a function symbol or a lambda expression
          to <see topic='@(url pseudo-termp)'>pseudo-terms</see>,
          obtaining a pseudo-term."
  :long
  "<p>
   If a lambda expression is applied, a beta reduction is performed.
   </p>
   @(def apply-term*)"
  (defmacro apply-term* (fn &rest terms)
    `(apply-term ,fn (list ,@terms))))

(define apply-unary-to-terms ((fn pseudo-fn/lambda-p) (terms pseudo-term-listp))
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
  ((define apply-unary-to-terms-aux ((fn pseudo-fn/lambda-p)
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

(defines all-program-ffn-symbs
  :parents (term-utilities)
  :short "Program-mode functions called by a term."
  :long
  "@(def all-program-ffn-symbs)
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
  (logic-fnsp (lambda-body lambd) wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))

(defines term-no-stobjs-p
  :mode :program
  :parents (term-utilities)
  :short "Check if a term has no @(see stobj)s."
  :long
  "<p>
   A term containing functions in @('*stobjs-out-invalid*')
   (on which @(tsee no-stobjs-p) would cause a guard violation),
   is regarded as having no stobjs,
   if all its other functions have no stobjs.
   </p>"

  (define term-no-stobjs-p ((term pseudo-termp) (wrld plist-worldp))
    :returns (yes/no "A @(tsee booleanp).")
    (or (variablep term)
        (fquotep term)
        (and (terms-no-stobjs-p (fargs term) wrld)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (or (member fn *stobjs-out-invalid*)
                       (no-stobjs-p fn wrld))
                 (term-no-stobjs-p (lambda-body fn) wrld))))))

  (define terms-no-stobjs-p ((terms pseudo-term-listp) (wrld plist-worldp))
    :returns (yes/no "A @(tsee booleanp).")
    (or (endp terms)
        (and (term-no-stobjs-p (car terms) wrld)
             (terms-no-stobjs-p (cdr terms) wrld)))))

(define lambda-no-stobjs-p
  ((lambd pseudo-lambdap) (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (term-utilities)
  :short "Check if a lambda expression has no @(see stobj)s,
          i.e. its body has no stobjs."
  (term-no-stobjs-p (lambda-body lambd) wrld))

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
   @(def guard-verified-fnsp)
   @(def guard-verified-fns-listp)"

  (define guard-verified-fnsp ((term (termp term wrld))
                               (wrld plist-worldp-with-formals))
    :returns (yes/no booleanp)
    (or (variablep term)
        (fquotep term)
        (and (guard-verified-fns-listp (fargs term) wrld)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (guard-verified-p fn wrld)
                 (guard-verified-fnsp (lambda-body fn) wrld))))))

  (define guard-verified-fns-listp ((terms (term-listp terms wrld))
                                    (wrld plist-worldp-with-formals))
    :returns (yes/no booleanp)
    (or (endp terms)
        (and (guard-verified-fnsp (car terms) wrld)
             (guard-verified-fns-listp (cdr terms) wrld)))))

(define lambda-guard-verified-fnsp ((lambd (lambdap lambd wrld))
                                    (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities)
  :short "Check if all the functions in a lambda expression
          are guard-verified."
  (guard-verified-fnsp (lambda-body lambd) wrld)
  :guard-hints (("Goal" :in-theory (enable lambdap))))

(defines guard-verified-exec-fnsp
  :parents (term-utilities)
  :short "Check if a term calls only guard-verified functions for execution."
  :long
  "<p>
   Check if all the functions that occur in the term,
   except possibly the ones in the @(':logic') subterms of @(tsee mbe)s,
   are guard-verified.
   The purpose of this function is to check whether a term
   could be potentially guard-verified.
   </p>
   <p>
   In translated form,
   a term @('(mbe :logic a :exec b)')
   appears as @('(return-last 'mbe1-raw b a)').
   So the code of this function treats this pattern specially.
   </p>
   @(def guard-verified-exec-fnsp)
   @(def guard-verified-exec-fns-listp)"
  :verify-guards nil

  (define guard-verified-exec-fnsp ((term (termp term wrld))
                                    (wrld plist-worldp-with-formals))
    :returns (yes/no booleanp)
    (b* (((when (variablep term)) t)
         ((when (fquotep term)) t)
         (fn/lambda (ffn-symb term))
         ((when (and (eq fn/lambda 'return-last)
                     (equal (fargn term 1) '(quote mbe1-raw))))
          (guard-verified-exec-fnsp (fargn term 2) wrld)))
      (if (symbolp fn/lambda)
          (and (guard-verified-p fn/lambda wrld)
               (guard-verified-exec-fns-listp (fargs term) wrld))
        (and (guard-verified-exec-fnsp (lambda-body fn/lambda) wrld)
             (guard-verified-exec-fns-listp (fargs term) wrld)))))

  (define guard-verified-exec-fns-listp ((terms (term-listp terms wrld))
                                         (wrld plist-worldp-with-formals))
    :returns (yes/no booleanp)
    (or (endp terms)
        (and (guard-verified-exec-fnsp (car terms) wrld)
             (guard-verified-exec-fns-listp (cdr terms) wrld)))))

(define lambda-guard-verified-exec-fnsp ((lambd (lambdap lambd wrld))
                                         (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (term-utilities)
  :short "Check if a lambda expression calls only guard-verified functions
          for execution."
  (guard-verified-exec-fnsp (lambda-body lambd) wrld))

(defines all-non-gv-exec-ffn-symbs
  :parents (term-utilities)
  :short "Non-guard-verified functions called by a term for execution."
  :long
  "<p>
   These are all the non-guard-verified functions that occur in the term,
   except those that occur in the @(':logic') subterms of @(tsee mbe)s.
   This is because, in order for a function to be guard-verified,
   the functions that occurs in such subterms do not have to be guard-verified.
   If this function returns @('nil'),
   the term could be potentially guard-verified.
   </p>
   <p>
   In translated form,
   a term @('(mbe :logic a :exec b)')
   appears as @('(return-last 'mbe1-raw b a)').
   So the code of this function treats this pattern specially.
   </p>
   @(def all-non-gv-exec-ffn-symbs)
   @(def all-non-gv-exec-ffn-symbs-lst)"
  :verify-guards nil

  (define all-non-gv-exec-ffn-symbs ((term pseudo-termp)
                                     (ans symbol-listp)
                                     (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn/lambda (ffn-symb term))
         ((when (and (eq fn/lambda 'return-last)
                     (equal (fargn term 1) '(quote mbe1-raw))))
          (all-non-gv-exec-ffn-symbs (fargn term 2) ans wrld))
         (ans (if (flambdap fn/lambda)
                  (all-non-gv-exec-ffn-symbs (lambda-body fn/lambda) ans wrld)
                (if (guard-verified-p fn/lambda wrld)
                    ans
                  (add-to-set-eq fn/lambda ans)))))
      (all-non-gv-exec-ffn-symbs-lst (fargs term) ans wrld)))

  (define all-non-gv-exec-ffn-symbs-lst ((terms pseudo-term-listp)
                                         (ans symbol-listp)
                                         (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (endp terms)) ans)
         (ans (all-non-gv-exec-ffn-symbs (car terms) ans wrld)))
      (all-non-gv-exec-ffn-symbs-lst (cdr terms) ans wrld))))

(define check-user-term (x (wrld plist-worldp))
  :returns (mv (term/message "A @(tsee pseudo-termp) or @('msgp')
                              (see @(tsee msg)).")
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
  :returns (mv (lambd/message  "A @(tsee pseudo-termp) or @('msgp')
                                (see @(tsee msg)).")
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
   a @('nil')-terminated list of exactly three elements,
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
        (mv (msg "~x0 is not a NIL-terminated list." x) nil))
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

(define trans-macro ((mac (macro-namep mac wrld)) (wrld plist-worldp))
  :returns (term "A @(tsee pseudo-termp).")
  :mode :program
  :parents (term-utilities)
  :short "Translated term that a call to a macro translates to."
  :long
  "<p>
   This function translates a call to the macro
   that only includes its required formal arguments,
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
   Furthermore, if the macro is sensitive
   to the &ldquo;shape&rdquo; of its arguments,
   calls with argument that are not the required formal arguments
   may yield different terms.
   </p>"
  (mv-let (term stobjs-out)
    (check-user-term (cons mac (macro-required-args mac wrld)) wrld)
    (declare (ignore stobjs-out))
    term))

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
       ((mv erp val) (guard-obligation term nil nil __function__ state))
       ((when erp)
        (raise "Error ~x0 when computing the guard obligation of ~x1."
               erp term))
       (obligation-clauses (cadr val))
       (obligation-formula (termify-clause-set obligation-clauses)))
    obligation-formula))
