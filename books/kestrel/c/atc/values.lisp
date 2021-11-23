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
(include-book "pointers")

(include-book "defthm-disjoint")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-values
  :parents (atc-dynamic-semantics)
  :short "A model of C values for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define fixtypes for values and related entities,
     and some basic ACL2 operations on them
     (these are not C operations, which are defined separately;
     they are just ACL2 operations on our model of values)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum value
  :short "Fixtype of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support the standard unsigned and signed integer values
     (except @('_Bool') values),
     as well as pointer values with any referenced type.
     (However, only some pointer values can be generated and used
     in our current dynamic semantics of C.)"))
  (:uchar uchar)
  (:schar schar)
  (:ushort ushort)
  (:sshort sshort)
  (:uint uint)
  (:sint sint)
  (:ulong ulong)
  (:slong slong)
  (:ullong ullong)
  (:sllong sllong)
  (:pointer pointer)
  :pred valuep
  :prepwork ((defthm-disjoint *value-disjoint-rules*
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
               pointerp)))

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
               (pointerp x)))
  :enable valuep
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value "values"
  :enable (errorp
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
           pointerp))

(defruled errorp-when-value-resultp-and-not-valuep
  (implies (and (value-resultp x)
                (not (valuep x)))
           (errorp x)))

(defrule value-resultp-possibilities
  (implies (value-resultp x)
           (or (valuep x)
               (errorp x)))
  :enable value-resultp
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist value-list
  :short "Fixtype of lists of values."
  :elt-type value
  :true-listp t
  :elementp-of-nil nil
  :pred value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value-list "lists of values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption value-option
  value
  :short "Fixtype of optional values."
  :pred value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value-option "optional values"
  :enable (errorp
           value-optionp
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
           pointerp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-signed-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a signed integer [C:6.2.5/4]."
  (b* ((val (value-fix val)))
    (or (scharp val)
        (sshortp val)
        (sintp val)
        (slongp val)
        (sllongp val)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-unsigned-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an unsigned integer [C:6.2.5/6]."
  (b* ((val (value-fix val)))
    (or (ucharp val)
        (ushortp val)
        (uintp val)
        (ulongp val)
        (ullongp val)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an integer [C:6.2.5/17]."
  (or (value-signed-integerp val)
      (value-unsigned-integerp val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-realp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a real [C:6.2.5/18]."
  (value-integerp val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-arithmeticp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is arithmetic [C:6.2.5/18]."
  (value-realp val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-scalarp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is scalar [C:6.2.5/21]."
  (or (value-arithmeticp val)
      (pointerp (value-fix val)))
  :hooks (:fix))

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
             value-signed-integerp))

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
             value-unsigned-integerp))

  (defrule not-errorp-when-valuep
    (implies (valuep x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable (scharp
             ucharp
             sshortp
             ushortp
             sintp
             uintp
             slongp
             ulongp
             sllongp
             ullongp
             pointerp
             valuep
             errorp))

  (defrule not-errorp-when-value-listp
    (implies (value-listp x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable errorp)

  (defrule not-errorp-when-value-optionp
    (implies (value-optionp x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable value-optionp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-value ((val valuep))
  :returns (type typep)
  :short "Type of a value."
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
          (t (prog2$ (impossible) (irr-type)))))
  :hooks (:fix)
  ///

  (defruled type-signed-integerp-of-type-of-signed-integer-value
    (implies (value-signed-integerp val)
             (type-signed-integerp (type-of-value val)))
    :enable value-signed-integerp)

  (defruled type-unsigned-integerp-of-type-of-unsigned-integer-value
    (implies (value-unsigned-integerp val)
             (type-unsigned-integerp (type-of-value val)))
    :enable value-unsigned-integerp)

  (defruled type-integerp-of-type-of-integer-value
    (implies (value-integerp val)
             (type-integerp (type-of-value val)))
    :enable (value-integerp
             value-signed-integerp
             value-unsigned-integerp))

  (defruled type-realp-of-type-of-real-value
    (implies (value-realp val)
             (type-realp (type-of-value val)))
    :enable (value-realp
             value-integerp
             value-signed-integerp
             value-unsigned-integerp))

  (defruled type-arithmeticp-of-type-of-arithmetic-value
    (implies (value-arithmeticp val)
             (type-arithmeticp (type-of-value val)))
    :enable (value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp
             value-unsigned-integerp))

  (defruled type-scalarp-of-type-of-scalar-value
    (implies (value-scalarp val)
             (type-scalarp (type-of-value val)))
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp
             value-unsigned-integerp
             type-scalarp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-value-option ((val? value-optionp))
  :returns (type typep)
  :short "Type of an optional value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the value if the value is present,
     while it is @('void') if the value is absent.
     This is a handy extension of @(tsee type-of-value),
     given that, in the dynamic semantics,
     we model computations that may return @('void') (e.g. function calls)
     as returning optional values, with @('nil') for no value."))
  (value-option-case val?
                     :some (type-of-value val?.val)
                     :none (type-void))
  :hooks (:fix))
