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

(include-book "../../language/dynamic-semantics")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-apconvert-rules
  :short "Rules about @(tsee apconvert-expr-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These leave most expression values unchanged,
     but they convert integer arrays with object designators to pointers."))

  (defruled apconvert-expr-value-when-not-value-array
    (implies (not (value-case x :array))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value x objdes)))
    :enable apconvert-expr-value)

  (defruled apconvert-expr-value-when-uchar-arrayp
    (implies (and (uchar-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-uchar))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-uchar-arrayp))

  (defruled apconvert-expr-value-when-schar-arrayp
    (implies (and (schar-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-schar))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-schar-arrayp))

  (defruled apconvert-expr-value-when-ushort-arrayp
    (implies (and (ushort-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-ushort))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-ushort-arrayp))

  (defruled apconvert-expr-value-when-sshort-arrayp
    (implies (and (sshort-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-sshort))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-sshort-arrayp))

  (defruled apconvert-expr-value-when-uint-arrayp
    (implies (and (uint-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-uint))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-uint-arrayp))

  (defruled apconvert-expr-value-when-sint-arrayp
    (implies (and (sint-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-sint))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-sint-arrayp))

  (defruled apconvert-expr-value-when-ulong-arrayp
    (implies (and (ulong-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-ulong))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-ulong-arrayp))

  (defruled apconvert-expr-value-when-slong-arrayp
    (implies (and (slong-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-slong))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-slong-arrayp))

  (defruled apconvert-expr-value-when-ullong-arrayp
    (implies (and (ullong-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-ullong))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-ullong-arrayp))

  (defruled apconvert-expr-value-when-sllong-arrayp
    (implies (and (sllong-arrayp x)
                  (objdesignp objdes))
             (equal (apconvert-expr-value (expr-value x objdes))
                    (expr-value (value-pointer (pointer-valid objdes)
                                               (type-sllong))
                                nil)))
    :enable (apconvert-expr-value
             value-array->elemtype-when-sllong-arrayp))

  (defruled apconvert-expr-value-when-not-value-array-alt
    (implies (not (equal (value-kind (expr-value->value eval)) :array))
             (equal (apconvert-expr-value eval)
                    (expr-value-fix eval)))
    :enable apconvert-expr-value)

  (defruled cintegerp-when-cintegerp-of-apconvert-expr-value
    (implies (and (expr-valuep (apconvert-expr-value eval))
                  (cintegerp (expr-value->value (apconvert-expr-value eval))))
             (cintegerp (expr-value->value eval)))
    :enable (apconvert-expr-value
             cintegerp))

  (defval *atc-apconvert-rules*
    '(apconvert-expr-value-when-not-value-array
      apconvert-expr-value-when-uchar-arrayp
      apconvert-expr-value-when-schar-arrayp
      apconvert-expr-value-when-ushort-arrayp
      apconvert-expr-value-when-sshort-arrayp
      apconvert-expr-value-when-uint-arrayp
      apconvert-expr-value-when-sint-arrayp
      apconvert-expr-value-when-ulong-arrayp
      apconvert-expr-value-when-slong-arrayp
      apconvert-expr-value-when-ullong-arrayp
      apconvert-expr-value-when-sllong-arrayp)))
