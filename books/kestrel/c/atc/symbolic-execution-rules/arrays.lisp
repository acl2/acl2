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

(include-book "../arrays")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection array-tau-rules
  :short "Some tau rules about arrays."

  (defrule not-errorp-when-arrayp
    (implies (or (schar-arrayp x)
                 (uchar-arrayp x)
                 (sshort-arrayp x)
                 (ushort-arrayp x)
                 (sint-arrayp x)
                 (uint-arrayp x)
                 (slong-arrayp x)
                 (ulong-arrayp x)
                 (sllong-arrayp x)
                 (ullong-arrayp x))
             (not (errorp x)))
    :rule-classes :tau-system
    :enable (schar-arrayp
             uchar-arrayp
             sshort-arrayp
             ushort-arrayp
             sint-arrayp
             uint-arrayp
             slong-arrayp
             ulong-arrayp
             sllong-arrayp
             ullong-arrayp
             errorp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection array-value-rules
  :short "Some rules about array values."

  (defrule valuep-when-uchar-arrayp
    (implies (uchar-arrayp x)
             (valuep x))
    :enable (valuep uchar-arrayp))

  (defrule valuep-when-schar-arrayp
    (implies (schar-arrayp x)
             (valuep x))
    :enable (valuep schar-arrayp))

  (defrule valuep-when-ushort-arrayp
    (implies (ushort-arrayp x)
             (valuep x))
    :enable (valuep ushort-arrayp))

  (defrule valuep-when-sshort-arrayp
    (implies (sshort-arrayp x)
             (valuep x))
    :enable (valuep sshort-arrayp))

  (defrule valuep-when-uint-arrayp
    (implies (uint-arrayp x)
             (valuep x))
    :enable (valuep uint-arrayp))

  (defrule valuep-when-sint-arrayp
    (implies (sint-arrayp x)
             (valuep x))
    :enable (valuep sint-arrayp))

  (defrule valuep-when-ulong-arrayp
    (implies (ulong-arrayp x)
             (valuep x))
    :enable (valuep ulong-arrayp))

  (defrule valuep-when-slong-arrayp
    (implies (slong-arrayp x)
             (valuep x))
    :enable (valuep slong-arrayp))

  (defrule valuep-when-ullong-arrayp
    (implies (ullong-arrayp x)
             (valuep x))
    :enable (valuep ullong-arrayp))

  (defrule valuep-when-sllong-arrayp
    (implies (sllong-arrayp x)
             (valuep x))
    :enable (valuep sllong-arrayp))

  (defrule value-kind-when-uchar-arrayp
    (implies (uchar-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind uchar-arrayp))

  (defrule value-kind-when-schar-arrayp
    (implies (schar-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind schar-arrayp))

  (defrule value-kind-when-ushort-arrayp
    (implies (ushort-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind ushort-arrayp))

  (defrule value-kind-when-sshort-arrayp
    (implies (sshort-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind sshort-arrayp))

  (defrule value-kind-when-uint-arrayp
    (implies (uint-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind uint-arrayp))

  (defrule value-kind-when-sint-arrayp
    (implies (sint-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind sint-arrayp))

  (defrule value-kind-when-ulong-arrayp
    (implies (ulong-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind ulong-arrayp))

  (defrule value-kind-when-slong-arrayp
    (implies (slong-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind slong-arrayp))

  (defrule value-kind-when-ullong-arrayp
    (implies (ullong-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind ullong-arrayp))

  (defrule value-kind-when-sllong-arrayp
    (implies (sllong-arrayp x)
             (equal (value-kind x)
                    :array))
    :enable (valuep value-kind sllong-arrayp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection array-value-disjoint-rules
  :short "Rules about disjointness of array values."
  (defthm-disjoint *array-value-disjoint-rules*
    uchar-arrayp
    schar-arrayp
    ushort-arrayp
    sshort-arrayp
    uint-arrayp
    sint-arrayp
    ulong-arrayp
    slong-arrayp
    ullong-arrayp
    sllong-arrayp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-of-value-under-array-predicates
  :short "Rules that rewrite @(tsee type-of-value) to specific types
          under hypotheses on different array types of values."

  (defruled type-of-value-when-uchar-arrayp
    (implies (uchar-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-uchar)
                                (value-array->length x))))
    :enable (type-of-value
             uchar-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-schar-arrayp
    (implies (schar-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-schar)
                                (value-array->length x))))
    :enable (type-of-value
             schar-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-ushort-arrayp
    (implies (ushort-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-ushort)
                                (value-array->length x))))
    :enable (type-of-value
             ushort-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-sshort-arrayp
    (implies (sshort-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-sshort)
                                (value-array->length x))))
    :enable (type-of-value
             sshort-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-uint-arrayp
    (implies (uint-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-uint)
                                (value-array->length x))))
    :enable (type-of-value
             uint-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-sint-arrayp
    (implies (sint-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-sint)
                                (value-array->length x))))
    :enable (type-of-value
             sint-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-ulong-arrayp
    (implies (ulong-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-ulong)
                                (value-array->length x))))
    :enable (type-of-value
             ulong-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-slong-arrayp
    (implies (slong-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-slong)
                                (value-array->length x))))
    :enable (type-of-value
             slong-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-ullong-arrayp
    (implies (ullong-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-ullong)
                                (value-array->length x))))
    :enable (type-of-value
             ullong-arrayp
             value-array->elemtype
             value-array->length))

  (defruled type-of-value-when-sllong-arrayp
    (implies (sllong-arrayp x)
             (equal (type-of-value x)
                    (type-array (type-sllong)
                                (value-array->length x))))
    :enable (type-of-value
             sllong-arrayp
             value-array->elemtype
             value-array->length)))
