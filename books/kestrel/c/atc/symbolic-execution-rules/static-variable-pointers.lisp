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

(include-book "../../language/pointer-operations")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-static-variable-pointer-rules
  :short "Rules about pointers to variables in static storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "When @(tsee exec-ident) is applied to a variable that contains an array,
     it is rewritten into a pointer to the variable,
     which must be in static storage:
     this produces a term of the form")
   (xdoc::codeblock
    "(value-pointer (pointer-valid (objdesign-static ...))"
    "               (value-array->elemtype ...))")
   (xdoc::p
    "This differs from the pointers to heap objects,
     which are ACL2 variables.")
   (xdoc::p
    "This pointer term must be showed valid,
     which we do via @('value-pointer-validp-of-value-pointer'),
     which produces
     @('(pointer-case (pointer-valid (objdesign-static ...)) :valid)'),
     which we resolve to @('t') via @('return-type-of-pointer-valid').")
   (xdoc::p
    "The type is extracted from the pointer,
     via @('value-pointer->reftype-of-value-pointer),
     which generates a term @('(type-fix ...)'),
     where @('...') is a term that constructs a type (e.g. @('(type-sint)')),
     so we use @('type-fix-when-typep'),
     along with rules saying that @(tsee type-sint) and similar constructors
     return types.")
   (xdoc::p
    "After establishing the non-nullness of the pointer,
     its designator is extracted, via @(tsee value-pointer->designator).
     The rule @('value-pointer->designator-of-value-pointer') does that,
     but leaves an @(tsee objdesign-fix) that needs to be removed,
     which we do via @('objdesign-fix-when-objdesignp')
     and @('return-type-of-objdesign-static').")
   (xdoc::p
    "The rule @('return-type-of-value-pointer') is used
     to establish that the pointer is in fact a value,
     which is needed to discharge certain conditions."))

  (defval *atc-static-variable-pointer-rules*
    '(value-pointer-validp-of-value-pointer
      return-type-of-pointer-valid
      value-pointer->reftype-of-value-pointer
      type-fix-when-typep
      return-type-of-type-schar
      return-type-of-type-uchar
      return-type-of-type-sshort
      return-type-of-type-ushort
      return-type-of-type-sint
      return-type-of-type-uint
      return-type-of-type-slong
      return-type-of-type-ulong
      return-type-of-type-sllong
      return-type-of-type-ullong
      value-pointer->designator-of-value-pointer
      objdesign-fix-when-objdesignp
      return-type-of-objdesign-static
      return-type-of-value-pointer)))
