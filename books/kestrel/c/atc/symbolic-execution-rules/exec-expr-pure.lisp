; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../proof-support/test-star")
(include-book "../../proof-support/pure-expression-execution")
(include-book "../../proof-support/exec-expr-pure-openers")

(include-book "../../representation/integer-operations")

(include-book "../../proof-support/syntaxp-for-expr-pure")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-rules
  :short "Rules for @(tsee exec-expr-pure)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We include the executable counterpart of @(tsee member-equal),
     needed to discharge the hypothesis of
     the rule for strict pure binary expressions.")
   (xdoc::p
    "We include executable counterparts of accessor functions for expressions,
     used to check the kind of expression and to retrieve its constituents."))

  (defval *atc-exec-expr-pure-rules*
    '(exec-expr-pure-when-ident
      exec-expr-pure-when-const
      exec-expr-pure-when-arrsub
      exec-expr-pure-when-member
      exec-expr-pure-when-memberp
      exec-expr-pure-when-arrsub-of-member
      exec-expr-pure-when-arrsub-of-memberp
      exec-expr-pure-when-unary
      exec-expr-pure-when-cast
      exec-expr-pure-when-strict-pure-binary
      exec-expr-pure-when-binary-logand
      exec-expr-pure-when-binary-logor
      sint-from-boolean-with-error-when-booleanp
      exec-expr-pure-apconvert-no-object-open
      exec-expr-pure-when-cond
      expr-valuep-of-expr-value
      expr-value->value-of-expr-value
      (:e member-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-pure-list-rules
  :short "Rules for @(tsee exec-expr-pure-list)."

  (defruled exec-expr-pure-list-of-nil
    (equal (exec-expr-pure-list nil compst)
           nil)
    :enable exec-expr-pure-list)

  (defruled exec-expr-pure-list-when-consp
    (implies (and (syntaxp (quotep es))
                  (consp es)
                  (equal eval (exec-expr-pure (car es) compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1))
                  (equal vals (exec-expr-pure-list (cdr es) compst))
                  (value-listp vals))
             (equal (exec-expr-pure-list es compst)
                    (cons val vals)))
    :enable exec-expr-pure-list)

  (defval *atc-exec-expr-pure-list-rules*
    '(exec-expr-pure-list-of-nil
      exec-expr-pure-list-when-consp)))
