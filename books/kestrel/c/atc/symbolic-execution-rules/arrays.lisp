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

(include-book "../arrays")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-array->elemtype-rules
  :short "Rules about @(tsee value-array->elemtype)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These turn @(tsee value-array->elemtype) into specific types
     given that the argument satisfies predicates like @(tsee uchar-arrayp).
     Hypotheses that arrays satisfy these predicates
     are in the generated theorems,
     so they can be discharged."))

  (defruled value-array->elemtype-when-uchar-arrayp
    (implies (uchar-arrayp x)
             (equal (value-array->elemtype x)
                    (type-uchar)))
    :enable (value-array->elemtype
             uchar-arrayp))

  (defruled value-array->elemtype-when-schar-arrayp
    (implies (schar-arrayp x)
             (equal (value-array->elemtype x)
                    (type-schar)))
    :enable (value-array->elemtype
             schar-arrayp))

  (defruled value-array->elemtype-when-ushort-arrayp
    (implies (ushort-arrayp x)
             (equal (value-array->elemtype x)
                    (type-ushort)))
    :enable (value-array->elemtype
             ushort-arrayp))

  (defruled value-array->elemtype-when-sshort-arrayp
    (implies (sshort-arrayp x)
             (equal (value-array->elemtype x)
                    (type-sshort)))
    :enable (value-array->elemtype
             sshort-arrayp))

  (defruled value-array->elemtype-when-uint-arrayp
    (implies (uint-arrayp x)
             (equal (value-array->elemtype x)
                    (type-uint)))
    :enable (value-array->elemtype
             uint-arrayp))

  (defruled value-array->elemtype-when-sint-arrayp
    (implies (sint-arrayp x)
             (equal (value-array->elemtype x)
                    (type-sint)))
    :enable (value-array->elemtype
             sint-arrayp))

  (defruled value-array->elemtype-when-ulong-arrayp
    (implies (ulong-arrayp x)
             (equal (value-array->elemtype x)
                    (type-ulong)))
    :enable (value-array->elemtype
             ulong-arrayp))

  (defruled value-array->elemtype-when-slong-arrayp
    (implies (slong-arrayp x)
             (equal (value-array->elemtype x)
                    (type-slong)))
    :enable (value-array->elemtype
             slong-arrayp))

  (defruled value-array->elemtype-when-ullong-arrayp
    (implies (ullong-arrayp x)
             (equal (value-array->elemtype x)
                    (type-ullong)))
    :enable (value-array->elemtype
             ullong-arrayp))

  (defruled value-array->elemtype-when-sllong-arrayp
    (implies (sllong-arrayp x)
             (equal (value-array->elemtype x)
                    (type-sllong)))
    :enable (value-array->elemtype
             sllong-arrayp))

  (defval *atc-value-array->elemtype-rules*
    '(value-array->elemtype-when-uchar-arrayp
      value-array->elemtype-when-schar-arrayp
      value-array->elemtype-when-ushort-arrayp
      value-array->elemtype-when-sshort-arrayp
      value-array->elemtype-when-uint-arrayp
      value-array->elemtype-when-sint-arrayp
      value-array->elemtype-when-ulong-arrayp
      value-array->elemtype-when-slong-arrayp
      value-array->elemtype-when-ullong-arrayp
      value-array->elemtype-when-sllong-arrayp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-array-length-rules
  :short "Rules for array length operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not operations in C, as we know,
     but we have functions in our C semantics for array length.
     We introduce rules to turn @(tsee value-array->length)
     into more specific array length functions like @(tsee uchar-array-length).
     We also add existing (i.e. proved elsewhere) rules
     about @(tsee uchar-array-length) and the others being @(tsee natp)."))

  (defruled array-length-when-uchar-array-length
    (implies (uchar-arrayp x)
             (equal (value-array->length x)
                    (uchar-array-length x)))
    :enable (value-array->length
             uchar-array-length
             uchar-array->elements
             value-array->elements))

  (defruled array-length-when-schar-array-length
    (implies (schar-arrayp x)
             (equal (value-array->length x)
                    (schar-array-length x)))
    :enable (value-array->length
             schar-array-length
             schar-array->elements
             value-array->elements))

  (defruled array-length-when-ushort-array-length
    (implies (ushort-arrayp x)
             (equal (value-array->length x)
                    (ushort-array-length x)))
    :enable (value-array->length
             ushort-array-length
             ushort-array->elements
             value-array->elements))

  (defruled array-length-when-sshort-array-length
    (implies (sshort-arrayp x)
             (equal (value-array->length x)
                    (sshort-array-length x)))
    :enable (value-array->length
             sshort-array-length
             sshort-array->elements
             value-array->elements))

  (defruled array-length-when-uint-array-length
    (implies (uint-arrayp x)
             (equal (value-array->length x)
                    (uint-array-length x)))
    :enable (value-array->length
             uint-array-length
             uint-array->elements
             value-array->elements))

  (defruled array-length-when-sint-array-length
    (implies (sint-arrayp x)
             (equal (value-array->length x)
                    (sint-array-length x)))
    :enable (value-array->length
             sint-array-length
             sint-array->elements
             value-array->elements))

  (defruled array-length-when-ulong-array-length
    (implies (ulong-arrayp x)
             (equal (value-array->length x)
                    (ulong-array-length x)))
    :enable (value-array->length
             ulong-array-length
             ulong-array->elements
             value-array->elements))

  (defruled array-length-when-slong-array-length
    (implies (slong-arrayp x)
             (equal (value-array->length x)
                    (slong-array-length x)))
    :enable (value-array->length
             slong-array-length
             slong-array->elements
             value-array->elements))

  (defruled array-length-when-ullong-array-length
    (implies (ullong-arrayp x)
             (equal (value-array->length x)
                    (ullong-array-length x)))
    :enable (value-array->length
             ullong-array-length
             ullong-array->elements
             value-array->elements))

  (defruled array-length-when-sllong-array-length
    (implies (sllong-arrayp x)
             (equal (value-array->length x)
                    (sllong-array-length x)))
    :enable (value-array->length
             sllong-array-length
             sllong-array->elements
             value-array->elements))

  (defval *atc-array-length-rules*
    '(array-length-when-uchar-array-length
      array-length-when-schar-array-length
      array-length-when-ushort-array-length
      array-length-when-sshort-array-length
      array-length-when-uint-array-length
      array-length-when-sint-array-length
      array-length-when-ulong-array-length
      array-length-when-slong-array-length
      array-length-when-ullong-array-length
      array-length-when-sllong-array-length
      natp-of-uchar-array-length
      natp-of-schar-array-length
      natp-of-ushort-array-length
      natp-of-sshort-array-length
      natp-of-uint-array-length
      natp-of-sint-array-length
      natp-of-ulong-array-length
      natp-of-slong-array-length
      natp-of-ullong-array-length
      natp-of-sllong-array-length)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-array-length-write-rules
  :short "Rules for array lengths and array write operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules say that the array write operations preserve array lengths.
     There is one rule for each @('<type1>-array-write-<type2>') function,
     so generate the list programmatically."))

  (define atc-array-length-write-rules-loop-itypes ((atype typep)
                                                    (itypes type-listp))
    :guard (and (type-nonchar-integerp atype)
                (type-nonchar-integer-listp itypes))
    :returns (names symbol-listp)
    :parents nil
    (cond ((endp itypes) nil)
          (t (b* ((afixtype (integer-type-to-fixtype atype))
                  (ifixtype (integer-type-to-fixtype (car itypes))))
               (cons
                (pack afixtype
                      '-array-length-of-
                      afixtype
                      '-array-write-
                      ifixtype)
                (atc-array-length-write-rules-loop-itypes atype
                                                          (cdr itypes)))))))

  (define atc-array-length-write-rules-loop-atypes ((atypes type-listp)
                                                    (itypes type-listp))
    :guard (and (type-nonchar-integer-listp atypes)
                (type-nonchar-integer-listp itypes))
    :returns (name symbol-listp)
    :parents nil
    (cond ((endp atypes) nil)
          (t (append (atc-array-length-write-rules-loop-itypes (car atypes)
                                                               itypes)
                     (atc-array-length-write-rules-loop-atypes (cdr atypes)
                                                               itypes)))))

  (defval *atc-array-length-write-rules*
    (atc-array-length-write-rules-loop-atypes *nonchar-integer-types*
                                              *nonchar-integer-types*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-array-read-rules
  :short "Rules about array reads."

  (defruled not-errorp-of-value-array-read-when-uchar-array-and-in-range
    (implies (and (c::uchar-arrayp array)
                  (integerp index)
                  (c::uchar-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::uchar-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-schar-array-and-in-range
    (implies (and (c::schar-arrayp array)
                  (integerp index)
                  (c::schar-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::schar-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-ushort-array-and-in-range
    (implies (and (c::ushort-arrayp array)
                  (integerp index)
                  (c::ushort-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::ushort-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-sshort-array-and-in-range
    (implies (and (c::sshort-arrayp array)
                  (integerp index)
                  (c::sshort-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::sshort-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-uint-array-and-in-range
    (implies (and (c::uint-arrayp array)
                  (integerp index)
                  (c::uint-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::uint-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-sint-array-and-in-range
    (implies (and (c::sint-arrayp array)
                  (integerp index)
                  (c::sint-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::sint-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-ulong-array-and-in-range
    (implies (and (c::ulong-arrayp array)
                  (integerp index)
                  (c::ulong-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::ulong-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-slong-array-and-in-range
    (implies (and (c::slong-arrayp array)
                  (integerp index)
                  (c::slong-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::slong-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-ullong-array-and-in-range
    (implies (and (c::ullong-arrayp array)
                  (integerp index)
                  (c::ullong-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::ullong-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled not-errorp-of-value-array-read-when-sllong-array-and-in-range
    (implies (and (c::sllong-arrayp array)
                  (integerp index)
                  (c::sllong-array-integer-index-okp array index))
             (not (c::errorp (c::value-array-read index array))))
    :use (:instance c::sllong-array-integer-read-alt-def
                    (index index) (array array)))

  (defruled value-array-read-when-uchar-arrayp
    (implies (and (uchar-arrayp x)
                  (cintegerp i)
                  (uchar-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (uchar-array-read x i)))
    :enable uchar-array-read-alt-def)

  (defruled value-array-read-when-schar-arrayp
    (implies (and (schar-arrayp x)
                  (cintegerp i)
                  (schar-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (schar-array-read x i)))
    :enable schar-array-read-alt-def)

  (defruled value-array-read-when-ushort-arrayp
    (implies (and (ushort-arrayp x)
                  (cintegerp i)
                  (ushort-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (ushort-array-read x i)))
    :enable ushort-array-read-alt-def)

  (defruled value-array-read-when-sshort-arrayp
    (implies (and (sshort-arrayp x)
                  (cintegerp i)
                  (sshort-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (sshort-array-read x i)))
    :enable sshort-array-read-alt-def)

  (defruled value-array-read-when-uint-arrayp
    (implies (and (uint-arrayp x)
                  (cintegerp i)
                  (uint-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (uint-array-read x i)))
    :enable uint-array-read-alt-def)

  (defruled value-array-read-when-sint-arrayp
    (implies (and (sint-arrayp x)
                  (cintegerp i)
                  (sint-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (sint-array-read x i)))
    :enable sint-array-read-alt-def)

  (defruled value-array-read-when-ulong-arrayp
    (implies (and (ulong-arrayp x)
                  (cintegerp i)
                  (ulong-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (ulong-array-read x i)))
    :enable ulong-array-read-alt-def)

  (defruled value-array-read-when-slong-arrayp
    (implies (and (slong-arrayp x)
                  (cintegerp i)
                  (slong-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (slong-array-read x i)))
    :enable slong-array-read-alt-def)

  (defruled value-array-read-when-ullong-arrayp
    (implies (and (ullong-arrayp x)
                  (cintegerp i)
                  (ullong-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (ullong-array-read x i)))
    :enable ullong-array-read-alt-def)

  (defruled value-array-read-when-sllong-arrayp
    (implies (and (sllong-arrayp x)
                  (cintegerp i)
                  (sllong-array-index-okp x i))
             (equal (value-array-read (integer-from-cinteger i) x)
                    (sllong-array-read x i)))
    :enable sllong-array-read-alt-def)

  (defval *atc-array-read-rules*
    '(not-errorp-of-value-array-read-when-uchar-array-and-in-range
      not-errorp-of-value-array-read-when-schar-array-and-in-range
      not-errorp-of-value-array-read-when-ushort-array-and-in-range
      not-errorp-of-value-array-read-when-sshort-array-and-in-range
      not-errorp-of-value-array-read-when-uint-array-and-in-range
      not-errorp-of-value-array-read-when-sint-array-and-in-range
      not-errorp-of-value-array-read-when-ulong-array-and-in-range
      not-errorp-of-value-array-read-when-slong-array-and-in-range
      not-errorp-of-value-array-read-when-ullong-array-and-in-range
      not-errorp-of-value-array-read-when-sllong-array-and-in-range)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-array-write-rules
  :short "Rules about array writes."

  (defruled value-array-write-when-uchar-arrayp
    (implies (and (uchar-arrayp x)
                  (cintegerp i)
                  (uchar-array-index-okp x i)
                  (ucharp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (uchar-array-write x i e)))
    :enable uchar-array-write-alt-def)

  (defruled value-array-write-when-schar-arrayp
    (implies (and (schar-arrayp x)
                  (cintegerp i)
                  (schar-array-index-okp x i)
                  (scharp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (schar-array-write x i e)))
    :enable schar-array-write-alt-def)

  (defruled value-array-write-when-ushort-arrayp
    (implies (and (ushort-arrayp x)
                  (cintegerp i)
                  (ushort-array-index-okp x i)
                  (ushortp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (ushort-array-write x i e)))
    :enable ushort-array-write-alt-def)

  (defruled value-array-write-when-sshort-arrayp
    (implies (and (sshort-arrayp x)
                  (cintegerp i)
                  (sshort-array-index-okp x i)
                  (sshortp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (sshort-array-write x i e)))
    :enable sshort-array-write-alt-def)

  (defruled value-array-write-when-uint-arrayp
    (implies (and (uint-arrayp x)
                  (cintegerp i)
                  (uint-array-index-okp x i)
                  (uintp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (uint-array-write x i e)))
    :enable uint-array-write-alt-def)

  (defruled value-array-write-when-sint-arrayp
    (implies (and (sint-arrayp x)
                  (cintegerp i)
                  (sint-array-index-okp x i)
                  (sintp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (sint-array-write x i e)))
    :enable sint-array-write-alt-def)

  (defruled value-array-write-when-ulong-arrayp
    (implies (and (ulong-arrayp x)
                  (cintegerp i)
                  (ulong-array-index-okp x i)
                  (ulongp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (ulong-array-write x i e)))
    :enable ulong-array-write-alt-def)

  (defruled value-array-write-when-slong-arrayp
    (implies (and (slong-arrayp x)
                  (cintegerp i)
                  (slong-array-index-okp x i)
                  (slongp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (slong-array-write x i e)))
    :enable slong-array-write-alt-def)

  (defruled value-array-write-when-ullong-arrayp
    (implies (and (ullong-arrayp x)
                  (cintegerp i)
                  (ullong-array-index-okp x i)
                  (ullongp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (ullong-array-write x i e)))
    :enable ullong-array-write-alt-def)

  (defruled value-array-write-when-sllong-arrayp
    (implies (and (sllong-arrayp x)
                  (cintegerp i)
                  (sllong-array-index-okp x i)
                  (sllongp e))
             (equal (value-array-write (integer-from-cinteger i) e x)
                    (sllong-array-write x i e)))
    :enable sllong-array-write-alt-def))
