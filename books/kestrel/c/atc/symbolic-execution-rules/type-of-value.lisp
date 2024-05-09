; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")
(include-book "arrays")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-type-of-value-rules
  :short "Rules about @(tsee type-of-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules rewrite @(tsee type-of-value) to specific types
     under hypotheses on different types of values
     that occur during symbolic execution."))

  (defruled type-of-value-when-value-pointer
    (implies (and (valuep x)
                  (value-case x :pointer))
             (equal (type-of-value x)
                    (type-pointer (value-pointer->reftype x))))
    :enable type-of-value)

  (defruled type-of-value-of-if*
    (equal (type-of-value (if* a b c))
           (if* a (type-of-value b) (type-of-value c)))
    :enable if*)

  (defval *atc-type-of-value-rules*
    '(type-of-value-when-ucharp
      type-of-value-when-scharp
      type-of-value-when-ushortp
      type-of-value-when-sshortp
      type-of-value-when-uintp
      type-of-value-when-sintp
      type-of-value-when-ulongp
      type-of-value-when-slongp
      type-of-value-when-ullongp
      type-of-value-when-sllongp
      type-of-value-when-value-pointer
      type-of-value-when-uchar-arrayp
      type-of-value-when-schar-arrayp
      type-of-value-when-ushort-arrayp
      type-of-value-when-sshort-arrayp
      type-of-value-when-uint-arrayp
      type-of-value-when-sint-arrayp
      type-of-value-when-ulong-arrayp
      type-of-value-when-slong-arrayp
      type-of-value-when-ullong-arrayp
      type-of-value-when-sllong-arrayp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-type-of-value-option-rules
  :short "Rules about @(tsee type-of-value-option)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules reduce @(tsee type-of-value-option)
     to @(tsee type-of-value) when the argument is a value,
     and to @('void') when the argument is @('nil').
     During execution, the argument is always either @('nil')
     or a term that is easily proved to be a value;
     so these rules suffice to eliminate @(tsee type-of-value-option)."))

  (defruled type-of-value-option-when-valuep
    (implies (valuep x)
             (equal (type-of-value-option x)
                    (type-of-value x)))
    :enable (type-of-value-option
             value-option-some->val))

  (defruled type-of-value-option-of-nil
    (equal (type-of-value-option nil)
           (type-void)))

  (defval *atc-type-of-value-option-rules*
    '(type-of-value-option-when-valuep
      type-of-value-option-of-nil)))
