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
    sllongp
    pointerp))

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
                 (pointerp x)
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
             pointerp
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
    :enable (valuep sllongp))

  (defrule valuep-when-pointerp
    (implies (pointerp x)
             (valuep x))
    :enable (valuep pointerp)))

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

(defruled type-of-value-alt-def
  :short "Alternative definition of @(tsee type-of-value)."
  (equal (type-of-value val)
         (b* ((val (value-fix val)))
           (cond ((ucharp val) (type-uchar))
                 ((scharp val) (type-schar))
                 ((ushortp val) (type-ushort))
                 ((sshortp val) (type-sshort))
                 ((uintp val) (type-uint))
                 ((sintp val) (type-sint))
                 ((ulongp val) (type-ulong))
                 ((slongp val) (type-slong))
                 ((ullongp val) (type-ullong))
                 ((sllongp val) (type-sllong))
                 ((pointerp val) (type-pointer (pointer->reftype val)))
                 ((value-case val :array) (make-type-array
                                           :of (value-array->elemtype val)
                                           :size nil))
                 ((value-case val :struct) (type-struct
                                            (value-struct->tag val)))
                 (t (prog2$ (impossible) (irr-type))))))
  :use (:instance lemma (val (value-fix val)))
  :prep-lemmas
  ((defruled lemma
     (implies (valuep val)
              (equal (type-of-value val)
                     (cond ((ucharp val) (type-uchar))
                           ((scharp val) (type-schar))
                           ((ushortp val) (type-ushort))
                           ((sshortp val) (type-sshort))
                           ((uintp val) (type-uint))
                           ((sintp val) (type-sint))
                           ((ulongp val) (type-ulong))
                           ((slongp val) (type-slong))
                           ((ullongp val) (type-ullong))
                           ((sllongp val) (type-sllong))
                           ((pointerp val)
                            (type-pointer (pointer->reftype val)))
                           ((value-case val :array)
                            (make-type-array :of (value-array->elemtype val)
                                             :size nil))
                           ((value-case val :struct)
                            (type-struct (value-struct->tag val)))
                           (t (prog2$ (impossible) (irr-type))))))
     :enable (type-of-value
              value-kind
              value-fix
              valuep
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
              pointerp
              pointer->reftype
              value-pointer->reftype
              value-array->elemtype))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-predicates-to-type-of-value-equalities
  :short "Rules that rewrite predicates for values
          to equalities of the types of the values."

  (local (in-theory (enable type-of-value-alt-def)))

  (defruled ucharp-to-type-of-value
    (implies (valuep x)
             (equal (ucharp x)
                    (equal (type-of-value x)
                           (type-uchar)))))

  (defruled scharp-to-type-of-value
    (implies (valuep x)
             (equal (scharp x)
                    (equal (type-of-value x)
                           (type-schar)))))

  (defruled ushortp-to-type-of-value
    (implies (valuep x)
             (equal (ushortp x)
                    (equal (type-of-value x)
                           (type-ushort)))))

  (defruled sshortp-to-type-of-value
    (implies (valuep x)
             (equal (sshortp x)
                    (equal (type-of-value x)
                           (type-sshort)))))

  (defruled uintp-to-type-of-value
    (implies (valuep x)
             (equal (uintp x)
                    (equal (type-of-value x)
                           (type-uint)))))

  (defruled sintp-to-type-of-value
    (implies (valuep x)
             (equal (sintp x)
                    (equal (type-of-value x)
                           (type-sint)))))

  (defruled ulongp-to-type-of-value
    (implies (valuep x)
             (equal (ulongp x)
                    (equal (type-of-value x)
                           (type-ulong)))))

  (defruled slongp-to-type-of-value
    (implies (valuep x)
             (equal (slongp x)
                    (equal (type-of-value x)
                           (type-slong)))))

  (defruled ullongp-to-type-of-value
    (implies (valuep x)
             (equal (ullongp x)
                    (equal (type-of-value x)
                           (type-ullong)))))

  (defruled sllongp-to-type-of-value
    (implies (valuep x)
             (equal (sllongp x)
                    (equal (type-of-value x)
                           (type-sllong)))))

  (defruled pointerp-to-type-of-value
    (implies (valuep x)
             (equal (pointerp x)
                    (equal (type-of-value x)
                           (type-pointer (pointer->reftype x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-predicates-to-type-of-value-forward
  :short "Forward-chaining rules from predicates for values
          to equalities of the types of the values."

  (local (in-theory (enable type-of-value-alt-def)))

  (defruled type-of-value-when-ucharp-forward
    (implies (ucharp x)
             (equal (type-of-value x)
                    (type-uchar))))

  (defruled type-of-value-when-scharp-forward
    (implies (scharp x)
             (equal (type-of-value x)
                    (type-schar))))

  (defruled type-of-value-when-ushortp-forward
    (implies (ushortp x)
             (equal (type-of-value x)
                    (type-ushort))))

  (defruled type-of-value-when-sshortp-forward
    (implies (sshortp x)
             (equal (type-of-value x)
                    (type-sshort))))

  (defruled type-of-value-when-uintp-forward
    (implies (uintp x)
             (equal (type-of-value x)
                    (type-uint))))

  (defruled type-of-value-when-sintp-forward
    (implies (sintp x)
             (equal (type-of-value x)
                    (type-sint))))

  (defruled type-of-value-when-ulongp-forward
    (implies (ulongp x)
             (equal (type-of-value x)
                    (type-ulong))))

  (defruled type-of-value-when-slongp-forward
    (implies (slongp x)
             (equal (type-of-value x)
                    (type-slong))))

  (defruled type-of-value-when-ullongp-forward
    (implies (ullongp x)
             (equal (type-of-value x)
                    (type-ullong))))

  (defruled type-of-value-when-sllongp-forward
    (implies (sllongp x)
             (equal (type-of-value x)
                    (type-sllong)))))
