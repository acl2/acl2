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

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/all-lambdas" :dir :system)
(include-book "kestrel/std/system/all-non-gv-exec-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/all-non-gv-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/all-program-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/apply-term" :dir :system)
(include-book "kestrel/std/system/apply-terms-same-args" :dir :system)
(include-book "kestrel/std/system/apply-unary-to-terms" :dir :system)
(include-book "kestrel/std/system/fapply-term" :dir :system)
(include-book "kestrel/std/system/fapply-terms-same-args" :dir :system)
(include-book "kestrel/std/system/fapply-unary-to-terms" :dir :system)
(include-book "kestrel/std/system/fsublis-fn" :dir :system)
(include-book "kestrel/std/system/fsublis-var" :dir :system)
(include-book "kestrel/std/system/guard-verified-exec-fnsp" :dir :system)
(include-book "kestrel/std/system/guard-verified-fnsp" :dir :system)
(include-book "kestrel/std/system/lambda-closedp" :dir :system)
(include-book "kestrel/std/system/lambda-guard-verified-exec-fnsp" :dir :system)
(include-book "kestrel/std/system/lambda-guard-verified-fnsp" :dir :system)
(include-book "kestrel/std/system/lambda-logic-fnsp" :dir :system)
(include-book "kestrel/std/system/term-function-recognizers" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "world-queries")

(local (include-book "all-vars-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-utilities
  :parents (system-utilities-non-built-in)
  :short "Utilities for @(see term)s.")

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
