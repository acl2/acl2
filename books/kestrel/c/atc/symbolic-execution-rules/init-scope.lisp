; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-init-scope-rules
  :short "Rules for @(tsee init-scope)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The base case is a call @('(init-scope nil nil)'),
     which is handled by the executable counterpart of @(tsee init-scope).
     For the step case, during symbolic execution we expect that
     there is always the same number of formals and actuals.")
   (xdoc::p
    "We need to enable @(tsee eq) because it arises from
     the translation of @('(obj-declor-case declor :pointer)')
     in one of the hypotheses of the rule."))

  (defruled init-scope-when-consp
    (implies (and (syntaxp (quotep formals))
                  (consp formals)
                  (equal formal (car formals))
                  (param-declonp formal)
                  (valuep val)
                  (equal name+tyname (param-declon-to-ident+tyname formal))
                  (equal name (mv-nth 0 name+tyname))
                  (equal tyname (mv-nth 1 name+tyname))
                  (equal (type-of-value val)
                         (tyname-to-type tyname))
                  (value-listp vals)
                  (equal scope (init-scope (cdr formals) vals))
                  (scopep scope)
                  (not (omap::in name scope)))
             (equal (init-scope formals (cons val vals))
                    (omap::update name val scope)))
    :enable init-scope)

  (defval *atc-init-scope-rules*
    '(init-scope-when-consp
      eq
      (:e init-scope)
      (:e param-declonp)
      (:e param-declon-to-ident+tyname))))
