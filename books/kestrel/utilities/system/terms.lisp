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
(include-book "kestrel/std/system/all-pkg-names" :dir :system)
(include-book "kestrel/std/system/all-program-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/apply-term" :dir :system)
(include-book "kestrel/std/system/apply-terms-same-args" :dir :system)
(include-book "kestrel/std/system/apply-unary-to-terms" :dir :system)
(include-book "kestrel/std/system/check-user-term" :dir :system)
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
(include-book "kestrel/std/system/term-guard-obligation" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "world-queries")

(local (include-book "all-vars-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-utilities
  :parents (system-utilities-non-built-in)
  :short "Utilities for @(see term)s.")

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
