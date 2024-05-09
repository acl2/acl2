; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

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
                  (not (equal (value-kind val) :array))
                  (equal name+tyname (param-declon-to-ident+tyname formal))
                  (equal name (mv-nth 0 name+tyname))
                  (equal tyname (mv-nth 1 name+tyname))
                  (equal (type-of-value val)
                         (adjust-type (tyname-to-type tyname)))
                  (value-listp vals)
                  (equal scope (init-scope (cdr formals) vals))
                  (scopep scope)
                  (not (omap::assoc name scope)))
             (equal (init-scope formals (cons val vals))
                    (omap::update name
                                  (remove-flexible-array-member val)
                                  scope)))
    :enable (init-scope apconvert-type))

  (defval *atc-init-scope-rules*
    '(init-scope-when-consp
      eq
      (:e init-scope)
      (:e param-declonp)
      (:e param-declon-to-ident+tyname)
      (:e obj-adeclor-array->size))))
