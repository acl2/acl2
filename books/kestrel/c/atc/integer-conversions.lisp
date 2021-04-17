; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")

(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-conversions
  :parents (atc-dynamic-semantics)
  :short "C integer conversions for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ACL2 functions that convert
     between values of different C integer types.
     In the ACL2 representation of C code for ATC,
     these explicit conversions are necessary,
     because the ACL2 representations of different C integer types
     are disjoint, i.e. there are no automatic inclusions.")
   (xdoc::p
    "Conversions between C types are described in [C:6.3].
     Here we define conversions between the integer types in our model;
     these conversions are described in [C:6.3.1.3].")
   (xdoc::p
    "For the case of a conversion to a signed integer
     that cannot represent the original value,
     we use a guard that rules out that case.
     This way, in order to use the conversion,
     it must be provably the case that
     the value is representable in the new signed integer type.
     This approach is similar to the one used for signed integer operations
     (see @(see atc-integer-operations)).")
   (xdoc::p
    "For the case of a conversion to an unsigned integer,
     we use @(tsee mod) to ensure it fits.
     If the original value fits, the @(tsee mod) has no effect.
     Otherwise, the @(tsee mod) corresponds to the
     repeated addition or subtraction described in [C:6.3.1.3]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-conversion (src-type dst-type)
  :guard (and (member-eq src-type *atc-integer-types*)
              (member-eq dst-type *atc-integer-types*))
  :returns (event pseudo-event-formp)
  :short "Event to generate a conversion between C integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conversion turns values of the source type
     into values of the destination type.
     If the two types are the same, no events are generated;
     we do not have the guard require the types to be different
     so that it is more convenient to call this macro repeatedly
     while looping through the source and destination types.")
   (xdoc::p
    "If the destination type is signed,
     and the source type is not included in the destination type,
     we generate not only the conversion,
     but also a function for the guard of the conversion,
     asserting that the original value is representable
     in the destination type."))

  (b* ((src-type-string (atc-integer-type-string src-type))
       (dst-type-string (atc-integer-type-string dst-type))
       (conv (acl2::packn-pos (list dst-type "-FROM-" src-type) 'atc))
       (conv-okp (add-suffix conv "-OKP"))
       (src-typep (atc-integer-typep src-type))
       (dst-typep (atc-integer-typep dst-type))
       (src-type->get (add-suffix src-type "->GET"))
       (dst-type-integerp (add-suffix dst-type "-INTEGERP"))
       (dst-type-integerp-alt-def (add-suffix dst-type "-INTEGERP-ALT-DEF"))
       (dst-type-mod (add-suffix dst-type "-MOD"))
       (diffp (not (eq src-type dst-type)))
       (signedp (atc-integer-type-signedp dst-type))
       (guardp (case dst-type
                 (schar t)
                 (sshort (not (eq src-type 'schar)))
                 (sint (not (member-eq src-type '(schar sshort))))
                 (slong (not (member-eq src-type '(schar sshort sint))))
                 (sllong (not (member-eq src-type '(schar sshort sint slong))))
                 (t nil))))

    `(progn

       ,@(and
          diffp
          signedp
          guardp
          `((define ,conv-okp ((x ,src-typep))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if a conversion from "
                                src-type-string
                                " to "
                                dst-type-string
                                " is well-defined.")
              (,dst-type-integerp (,src-type->get x))
              :hooks (:fix))))

       ,@(and
          diffp
          `((define ,conv ((x ,src-typep))
              ,@(and guardp `(:guard (,conv-okp x)))
              :returns (result ,dst-typep)
              :short ,(str::cat "Convert from "
                                src-type-string
                                " to "
                                dst-type-string
                                "').")
              (,(if signedp dst-type dst-type-mod) (,src-type->get x))
              :guard-hints (("Goal"
                             :in-theory (enable ,(if guardp
                                                     conv-okp
                                                   dst-type-integerp-alt-def))))
              :hooks (:fix)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-conversions-loop-inner (src-type dst-types)
  :guard (and (true-listp dst-types)
              (subsetp-eq (cons src-type dst-types) *atc-integer-types*))
  :returns (event pseudo-event-form-listp)
  :short "Events to generate the integer conversions between
          a source type and a list of destination types."
  (cond ((endp dst-types) nil)
        (t (cons
            (atc-def-integer-conversion src-type (car dst-types))
            (atc-def-integer-conversions-loop-inner src-type
                                                    (cdr dst-types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-conversions-loop-outer (src-types dst-types)
  :guard (and (true-listp src-types)
              (true-listp dst-types)
              (subsetp-eq (append src-types dst-types) *atc-integer-types*))
  :returns (event pseudo-event-form-listp)
  :short "Events to generate the integer conversions between
          a list of source types and a list of destination types."
  (cond ((endp src-types) nil)
        (t (append
            (atc-def-integer-conversions-loop-inner (car src-types)
                                                    dst-types)
            (atc-def-integer-conversions-loop-outer (cdr src-types)
                                                    dst-types))))
  :prepwork ((local (include-book "std/lists/sets" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ atc-def-integer-conversions ()
  :short "Macro to generate all the integer conversions in our model."
  `(progn ,@(atc-def-integer-conversions-loop-outer *atc-integer-types*
                                                    *atc-integer-types*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(atc-def-integer-conversions)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-conversions-signed-from-unsigned-okp
  :short "Theorems about certain conversions from unsigned to signed
          being always allowed for certain integer type sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove these theorems in a general way,
     with hypotheses on the integer type sizes,
     disabling the rules that may otherwise obviate the hypotheses."))

  (defrule sint-from-uchar-okp-when-uchar-max-<=-sint-max
    (implies (<= (uchar-max) (sint-max))
             (sint-from-uchar-okp x))
    :enable (sint-from-uchar-okp sint-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uint-max-vs-slong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sint-from-ushort-okp-when-ushort-max-<=-sint-max
    (implies (<= (ushort-max) (sint-max))
             (sint-from-ushort-okp x))
    :enable (sint-from-ushort-okp sint-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uint-max-vs-slong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule slong-from-uint-okp-when-uint-max-<=slong-max
    (implies (<= (uint-max) (slong-max))
             (slong-from-uint-okp x))
    :enable (slong-from-uint-okp slong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uint-max-vs-slong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sllong-from-uint-okp-when-uint-max-<=sllong-max
    (implies (<= (uint-max) (sllong-max))
             (slong-from-uint-okp x))
    :enable (sllong-from-uint-okp sllong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uint-max-vs-slong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sllong-from-ulong-okp-when-ulong-max-<=sllong-max
    (implies (<= (ulong-max) (sllong-max))
             (sllong-from-ulong-okp x))
    :enable (sllong-from-ulong-okp sllong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uint-max-vs-slong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max)))
