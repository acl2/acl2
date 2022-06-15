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

(include-book "integers")
(include-book "types")

(include-book "../language/values")
(include-book "../language/pointer-operations")
(include-book "../language/array-operations")
(include-book "../language/structure-operations")

(include-book "defthm-disjoint")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-values
  :parents (atc-dynamic-semantics)
  :short "C values for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATC uses the "
    (xdoc::seetopic "values" "model of C values")
    " from the language formalization for various purposes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-value-disjoint-rules
  :short "Rules about disjointness of integer values."

  (local (in-theory (enable value-kind)))

  (defthm-disjoint *integer-value-disjoint-rules*
    ucharp
    scharp
    ushortp
    sshortp
    uintp
    sintp
    ulongp
    slongp
    ullongp
    sllongp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-more-theorems
  :short "Additional theorems about values."

  (defrule valuep-possibilities
    (implies (valuep x)
             (or (ucharp x)
                 (scharp x)
                 (ushortp x)
                 (sshortp x)
                 (uintp x)
                 (sintp x)
                 (ulongp x)
                 (slongp x)
                 (ullongp x)
                 (sllongp x)
                 (value-case x :pointer)
                 (value-case x :array)
                 (value-case x :struct)))
    :enable (valuep
             ucharp
             scharp
             ushortp
             sshortp
             uintp
             sintp
             ulongp
             slongp
             ullongp
             sllongp
             value-kind)
    :rule-classes :forward-chaining)

  (defrule valuep-when-ucharp
    (implies (ucharp x)
             (valuep x))
    :enable (valuep ucharp))

  (defrule valuep-when-scharp
    (implies (scharp x)
             (valuep x))
    :enable (valuep scharp))

  (defrule valuep-when-ushortp
    (implies (ushortp x)
             (valuep x))
    :enable (valuep ushortp))

  (defrule valuep-when-sshortp
    (implies (sshortp x)
             (valuep x))
    :enable (valuep sshortp))

  (defrule valuep-when-uintp
    (implies (uintp x)
             (valuep x))
    :enable (valuep uintp))

  (defrule valuep-when-sintp
    (implies (sintp x)
             (valuep x))
    :enable (valuep sintp))

  (defrule valuep-when-ulongp
    (implies (ulongp x)
             (valuep x))
    :enable (valuep ulongp))

  (defrule valuep-when-slongp
    (implies (slongp x)
             (valuep x))
    :enable (valuep slongp))

  (defrule valuep-when-ullongp
    (implies (ullongp x)
             (valuep x))
    :enable (valuep ullongp))

  (defrule valuep-when-sllongp
    (implies (sllongp x)
             (valuep x))
    :enable (valuep sllongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-list-more-theorems
  :short "Additional theorems about lists of values."

  (defrule value-listp-when-uchar-listp
    (implies (uchar-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-schar-listp
    (implies (schar-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ushort-listp
    (implies (ushort-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sshort-listp
    (implies (sshort-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-uint-listp
    (implies (uint-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sint-listp
    (implies (sint-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ulong-listp
    (implies (ulong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-slong-listp
    (implies (slong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ullong-listp
    (implies (ullong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sllong-listp
    (implies (sllong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled value-signed-integerp-alt-def
  :short "Alternative definition of @(tsee value-signed-integerp)."
  (equal (value-signed-integerp val)
         (b* ((val (value-fix val)))
           (or (scharp val)
               (sshortp val)
               (sintp val)
               (slongp val)
               (sllongp val))))
  :use (:instance lemma (val (value-fix val)))
  :prep-lemmas
  ((defruled lemma
     (implies (valuep val)
              (equal (value-signed-integerp val)
                     (or (scharp val)
                         (sshortp val)
                         (sintp val)
                         (slongp val)
                         (sllongp val))))
     :enable (valuep
              value-kind
              value-signed-integerp
              scharp
              sshortp
              sintp
              slongp
              sllongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled value-unsigned-integerp-alt-def
  :short "Alternative definition of @(tsee value-unsigned-integerp)."
  (equal (value-unsigned-integerp val)
         (b* ((val (value-fix val)))
           (or (ucharp val)
               (ushortp val)
               (uintp val)
               (ulongp val)
               (ullongp val))))
  :use (:instance lemma (val (value-fix val)))
  :prep-lemmas
  ((defruled lemma
     (implies (valuep val)
              (equal (value-unsigned-integerp val)
                     (or (ucharp val)
                         (ushortp val)
                         (uintp val)
                         (ulongp val)
                         (ullongp val))))
     :enable (valuep
              value-kind
              value-unsigned-integerp
              ucharp
              ushortp
              uintp
              ulongp
              ullongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-tau-rules
  :short "Some tau rules about values."

  (defrule signed-integer-value-kinds
    (implies (or (scharp x)
                 (sshortp x)
                 (sintp x)
                 (slongp x)
                 (sllongp x))
             (and (value-scalarp x)
                  (value-arithmeticp x)
                  (value-realp x)
                  (value-integerp x)
                  (value-signed-integerp x)))
    :rule-classes :tau-system
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp-alt-def))

  (defrule unsigned-integer-value-kinds
    (implies (or (ucharp x)
                 (ushortp x)
                 (uintp x)
                 (ulongp x)
                 (ullongp x))
             (and (value-scalarp x)
                  (value-arithmeticp x)
                  (value-realp x)
                  (value-integerp x)
                  (value-unsigned-integerp x)))
    :rule-classes :tau-system
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-unsigned-integerp-alt-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-predicates-to-type-of-value-equalities
  :short "Rules that rewrite predicates for values
          to equalities of the types of the values."

  (defruled ucharp-to-type-of-value
    (implies (valuep x)
             (equal (ucharp x)
                    (equal (type-of-value x)
                           (type-uchar))))
    :enable (type-of-value
             valuep
             value-kind
             ucharp))

  (defruled scharp-to-type-of-value
    (implies (valuep x)
             (equal (scharp x)
                    (equal (type-of-value x)
                           (type-schar))))
    :enable (type-of-value
             valuep
             value-kind
             scharp))

  (defruled ushortp-to-type-of-value
    (implies (valuep x)
             (equal (ushortp x)
                    (equal (type-of-value x)
                           (type-ushort))))
    :enable (type-of-value
             valuep
             value-kind
             ushortp))

  (defruled sshortp-to-type-of-value
    (implies (valuep x)
             (equal (sshortp x)
                    (equal (type-of-value x)
                           (type-sshort))))
    :enable (type-of-value
             valuep
             value-kind
             sshortp))

  (defruled uintp-to-type-of-value
    (implies (valuep x)
             (equal (uintp x)
                    (equal (type-of-value x)
                           (type-uint))))
    :enable (type-of-value
             valuep
             value-kind
             uintp))

  (defruled sintp-to-type-of-value
    (implies (valuep x)
             (equal (sintp x)
                    (equal (type-of-value x)
                           (type-sint))))
    :enable (type-of-value
             valuep
             value-kind
             sintp))

  (defruled ulongp-to-type-of-value
    (implies (valuep x)
             (equal (ulongp x)
                    (equal (type-of-value x)
                           (type-ulong))))
    :enable (type-of-value
             valuep
             value-kind
             ulongp))

  (defruled slongp-to-type-of-value
    (implies (valuep x)
             (equal (slongp x)
                    (equal (type-of-value x)
                           (type-slong))))
    :enable (type-of-value
             valuep
             value-kind
             slongp))

  (defruled ullongp-to-type-of-value
    (implies (valuep x)
             (equal (ullongp x)
                    (equal (type-of-value x)
                           (type-ullong))))
    :enable (type-of-value
             valuep
             value-kind
             ullongp))

  (defruled sllongp-to-type-of-value
    (implies (valuep x)
             (equal (sllongp x)
                    (equal (type-of-value x)
                           (type-sllong))))
    :enable (type-of-value
             valuep
             value-kind
             sllongp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-of-value-under-value-predicates
  :short "Rules that rewrite @(tsee type-of-value) to specific types
          under hypotheses on different types of values."

  (defruled type-of-value-when-ucharp
    (implies (ucharp x)
             (equal (type-of-value x)
                    (type-uchar)))
    :enable (type-of-value
             value-kind
             ucharp))

  (defruled type-of-value-when-scharp
    (implies (scharp x)
             (equal (type-of-value x)
                    (type-schar)))
    :enable (type-of-value
             value-kind
             scharp))

  (defruled type-of-value-when-ushortp
    (implies (ushortp x)
             (equal (type-of-value x)
                    (type-ushort)))
    :enable (type-of-value
             value-kind
             ushortp))

  (defruled type-of-value-when-sshortp
    (implies (sshortp x)
             (equal (type-of-value x)
                    (type-sshort)))
    :enable (type-of-value
             value-kind
             sshortp))

  (defruled type-of-value-when-uintp
    (implies (uintp x)
             (equal (type-of-value x)
                    (type-uint)))
    :enable (type-of-value
             value-kind
             uintp))

  (defruled type-of-value-when-sintp
    (implies (sintp x)
             (equal (type-of-value x)
                    (type-sint)))
    :enable (type-of-value
             value-kind
             sintp))

  (defruled type-of-value-when-ulongp
    (implies (ulongp x)
             (equal (type-of-value x)
                    (type-ulong)))
    :enable (type-of-value
             value-kind
             ulongp))

  (defruled type-of-value-when-slongp
    (implies (slongp x)
             (equal (type-of-value x)
                    (type-slong)))
    :enable (type-of-value
             value-kind
             slongp))

  (defruled type-of-value-when-ullongp
    (implies (ullongp x)
             (equal (type-of-value x)
                    (type-ullong)))
    :enable (type-of-value
             value-kind
             ullongp))

  (defruled type-of-value-when-sllongp
    (implies (sllongp x)
             (equal (type-of-value x)
                    (type-sllong)))
    :enable (type-of-value
             value-kind
             sllongp))

  (defruled type-of-value-when-value-pointer
    (implies (and (valuep x)
                  (value-case x :pointer))
             (equal (type-of-value x)
                    (type-pointer (value-pointer->reftype x))))
    :enable type-of-value))
