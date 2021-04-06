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

(include-book "integer-values")
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
  :hooks (:fix))
