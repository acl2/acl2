; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")
(include-book "static-semantics")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-operations
  :parents (language)
  :short "Operations on C integers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer->get ((val valuep))
  :guard (value-integerp val)
  :returns (mathint integerp)
  :short "Turn a C integer value into a mathematical (i.e. ACL2) integer."
  (value-case val
              :uchar val.get
              :schar val.get
              :ushort val.get
              :sshort val.get
              :uint val.get
              :sint val.get
              :ulong val.get
              :slong val.get
              :ullong val.get
              :sllong val.get
              :pointer (ifix (impossible))
              :array (ifix (impossible))
              :struct (ifix (impossible)))
  :guard-hints (("Goal" :in-theory (enable value-integerp
                                           value-signed-integerp
                                           value-unsigned-integerp)))
  :hooks (:fix)
  ///

  (defrule value-integer->get-bounds
    (and (<= (integer-type-min (type-of-value val))
             (value-integer->get val))
         (<= (value-integer->get val)
             (integer-type-max (type-of-value val))))
    :rule-classes ((:linear :trigger-terms ((value-integer->get val))))
    :enable (integer-type-min
             integer-type-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer ((mathint integerp) (type typep))
  :guard (and (type-nonchar-integerp type)
              (integer-type-rangep mathint type))
  :returns (val valuep)
  :short "Turn a mathematical (i.e. ACL2) integer into a C integer value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the C integer value is passed as parameter to this function.")
   (xdoc::p
    "We exclude the plain @('char') type for now,
     because our model of values does not yet include plain @('char').")
   (xdoc::p
    "We require, in the guard, the integer to be representable
     in the range of the integer type."))
  (b* ((mathint (ifix mathint)))
    (case (type-kind type)
      (:uchar (value-uchar mathint))
      (:schar (value-schar mathint))
      (:ushort (value-ushort mathint))
      (:sshort (value-sshort mathint))
      (:uint (value-uint mathint))
      (:sint (value-sint mathint))
      (:ulong (value-ulong mathint))
      (:slong (value-slong mathint))
      (:ullong (value-ullong mathint))
      (:sllong (value-sllong mathint))
      (t (value-fix (impossible)))))
  :guard-hints (("Goal" :in-theory (enable integer-type-rangep
                                           integer-type-min
                                           integer-type-max
                                           uchar-integerp-alt-def
                                           schar-integerp-alt-def
                                           ushort-integerp-alt-def
                                           sshort-integerp-alt-def
                                           uint-integerp-alt-def
                                           sint-integerp-alt-def
                                           ulong-integerp-alt-def
                                           slong-integerp-alt-def
                                           ullong-integerp-alt-def
                                           sllong-integerp-alt-def
                                           type-nonchar-integerp)))
  :hooks (:fix)
  ///

  (defrule type-of-value-of-value-integer
    (implies (type-nonchar-integerp type)
             (equal (type-of-value (value-integer mathint type))
                    (type-fix type)))
    :enable (type-of-value
             type-nonchar-integerp))

  (defrule value-kind-of-value-integer
    (implies (type-nonchar-integerp type)
             (equal (value-kind (value-integer mathint type))
                    (type-kind type)))
    :enable type-nonchar-integerp)

  (defrule value-integerp-of-value-integer
    (implies (type-nonchar-integerp type)
             (value-integerp (value-integer mathint type)))
    :enable (value-integerp
             value-signed-integerp
             value-unsigned-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-integer-and-value-integer->get
  :short "Theorems about @(tsee value-integer) and @(tsee value-integer->get)."

  (defrule value-integer-of-value-integer->get-when-type-of-value
    (implies (and (value-integerp val)
                  (equal type (type-of-value val)))
             (equal (value-integer (value-integer->get val) type)
                    (value-fix val)))
    :enable (value-integer
             value-integer->get
             value-integerp
             value-unsigned-integerp
             value-signed-integerp
             fix
             ifix))

  (defrule value-integer->get-of-value-integer
    (b* ((val (value-integer mathint type)))
      (implies (and (type-nonchar-integerp type)
                    (integer-type-rangep mathint type))
               (equal (value-integer->get val)
                      (ifix mathint))))
    :enable (value-integer
             value-integer->get
             integer-type-rangep
             integer-type-min
             integer-type-max
             uchar-integerp-alt-def
             schar-integerp-alt-def
             ushort-integerp-alt-def
             sshort-integerp-alt-def
             uint-integerp-alt-def
             sint-integerp-alt-def
             ulong-integerp-alt-def
             slong-integerp-alt-def
             ullong-integerp-alt-def
             sllong-integerp-alt-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test-integer-value ((val valuep))
  :guard (value-integerp val)
  :returns (res booleanp)
  :short "Test an integer value logically."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some contexts (e.g. conditional tests),
     an integer is treated as a logical boolean:
     false if 0, true if not 0.
     This is captured by this ACL2 function."))
  (not (equal (value-integer->get val) 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define convert-integer-value ((val valuep) (type typep))
  :guard (and (value-integerp val)
              (type-nonchar-integerp type))
  :returns (newval value-resultp)
  :short "Convert an integer value to an integer type [C17:6.3.1.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We extract the underlying mathematical (i.e. ACL2) integer from the value,
     and we attempt to contruct an integer value of the new type from it.
     If the new type is unsigned,
     the mathematical integer is reduced
     modulo one plus the maximum value of the unsigned type [C17:6.3.1.3/2];
     this always works, i.e. no error is ever returned.
     If the new type is signed, there are two cases [C17:6.3.1.3/3]:
     if the mathematical integer fits in the type,
     we return a value of that type with that integer;
     otherwise, we return an error.")
   (xdoc::p
    "We do not yet support conversions to the plain @('char') type;
     this restriction is expressed by the guard.
     However, we prefer to keep the name of this function more general,
     in anticipation for extending it to those two types.")
   (xdoc::p
    "We prove a theorem showing that converting a value to its type
     is a no-op, i.e. it leaves the value unchanged.")
   (xdoc::p
    "We prove a theorem saying that conversions to unsigned types
     never yields errors.")
   (xdoc::p
    "We also prove two theorems saying that
     converting signed @('char')s and signed @('short')s
     to signed @('int')s
     never yields errors,
     as well as two theorems saying that
     converting unsigned @('char')s and unsigned @('short')s
     to signed @('int')s,
     provided the range of the latter
     includes the ranges of the former,
     never yields errors.")
   (xdoc::p
    "These last four theorems are relevant to
     the use of integer conversions in @(tsee promote-value),
     to show that that function never yields errors;
     however, they are more general theorems about integer conversions.
     Also the first two theorems mentioned above
     are in fact relevant to showing that @(tsee promote-value) yields no error,
     but they are clearly more general in nature."))
  (b* ((mathint (value-integer->get val)))
    (cond ((type-unsigned-integerp type)
           (value-integer (mod mathint (1+ (integer-type-max type)))
                          type))
          ((integer-type-rangep mathint type) (value-integer mathint type))
          (t (error (list :out-of-range (value-fix val) (type-fix type))))))
  :guard-hints (("Goal" :in-theory (enable integer-type-rangep ifix)))
  :hooks (:fix)
  ///

  (defret type-of-value-of-convert-integer-value
    (implies (not (errorp newval))
             (equal (type-of-value newval)
                    (type-fix type)))
    :hyp (type-nonchar-integerp type))

  (defret value-kind-of-convert-integer-value
    (implies (and (not (errorp newval))
                  (type-nonchar-integerp type))
             (equal (value-kind newval)
                    (type-kind type))))

  (defret value-integerp-of-convert-integer-value
    (implies (not (errorp newval))
             (value-integerp newval))
    :hyp (type-nonchar-integerp type))

  (defruled convert-integer-value-to-type-of-value
    (implies (and (value-integerp val)
                  (equal type (type-of-value val)))
             (equal (convert-integer-value val type)
                    (value-fix val)))
    :enable (value-unsigned-integerp
             integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-to-unsigned
    (implies (type-unsigned-integerp type)
             (valuep (convert-integer-value val type))))

  (defruled valuep-of-convert-integer-value-from-schar-to-sint
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-schar-to-slong
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-schar-to-sllong
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-sshort-to-sint
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-sshort-to-slong
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-sshort-to-sllong
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-sint-to-slong
    (implies (value-case val :sint)
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-sint-to-sllong
    (implies (value-case val :sint)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-slong-to-sllong
    (implies (value-case val :slong)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-uchar-to-sint
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-uchar-to-slong
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (slong-max)))
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-uchar-to-sllong
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-ushort-to-sint
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-ushort-to-slong
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (slong-max)))
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-ushort-to-sllong
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-uint-to-slong
    (implies (and (value-case val :uint)
                  (<= (uint-max) (slong-max)))
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-uint-to-sllong
    (implies (and (value-case val :uint)
                  (<= (uint-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix))

  (defruled valuep-of-convert-integer-value-from-ulong-to-sllong
    (implies (and (value-case val :ulong)
                  (<= (ulong-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             ifix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define promote-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (promoted-val valuep
                         :hints
                         (("Goal"
                           :in-theory
                           (enable promote-value-not-error-lemma))))
  :short "Apply the integer promotions to a value [C17:6.3.1.1/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee promote-type).
     See the documentation of that function for details.
     Here we actually convert values;
     we do not merely compute a promoted type.")
   (xdoc::p
    "We promote the type of the value,
     obtaining the type of the new value.
     If the starting value is an integer one,
     in which case the promoted type is also an integer one,
     we convert the value to the promoted type.
     The other case, i.e. that the starting value is not an integer one,
     cannot happens under the guard,
     given that in our current model
     all the arithmetic values are integer values.
     But if/when we extend our model with more arithmetic values,
     then this code does not have to change.")
   (xdoc::p
    "This function never returns error:
     promotion always works.
     To show this, we need to show that @(tsee convert-integer-value)
     never returns errors when used to promote values,
     which we do via rules about @(tsee convert-integer-value)."))
  (b* ((type (promote-type (type-of-value val))))
    (if (value-integerp val)
        (convert-integer-value val type)
      (value-fix val)))

  :prepwork
  ((defruled promote-value-not-error-lemma
     (implies (value-integerp val)
              (valuep
               (convert-integer-value val
                                      (promote-type (type-of-value val)))))
     :enable (promote-type
              convert-integer-value-to-type-of-value
              valuep-of-convert-integer-value-to-unsigned
              valuep-of-convert-integer-value-from-schar-to-sint
              valuep-of-convert-integer-value-from-sshort-to-sint
              valuep-of-convert-integer-value-from-uchar-to-sint
              valuep-of-convert-integer-value-from-ushort-to-sint)
     :disable ((:e type-sint))))

  :hooks (:fix)

  ///

  (defruled type-of-value-of-promote-value
    (equal (type-of-value (promote-value val))
           (promote-type (type-of-value val)))
    :enable (promote-value-not-error-lemma
             not-errorp-when-valuep
             promote-type-when-not-type-integerp))

  (defrule value-arithmeticp-of-promote-value
    (equal (value-arithmeticp (promote-value val))
           (value-arithmeticp val))
    :enable (promote-value-not-error-lemma
             not-errorp-when-valuep
             value-arithmeticp
             value-realp))

  (defrule value-promoted-arithmeticp-of-promote-value
    (equal (value-promoted-arithmeticp (promote-value val))
           (value-arithmeticp val))
    :enable (promote-value-not-error-lemma
             not-errorp-when-valuep
             value-promoted-arithmeticp
             value-arithmeticp
             value-realp))

  (defrule value-integerp-of-promote-value
    (equal (value-integerp (promote-value val))
           (value-integerp val))
    :enable (promote-value-not-error-lemma
             not-errorp-when-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uaconvert-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (mv (new-val1 valuep)
               (new-val2 valuep))
  :short "Apply the usual arithmetic conversions to two arithmetic values
          [C17:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee uaconvert-types).
     See the documentation of that function for details.
     Here we actually convert the values;
     we do not merely compute the common type.")
   (xdoc::p
    "We convert the types of the values,
     obtaining the type of the new values.
     Then we convert each value to the new type.
     In our current model all the arithmetic values are integer values,
     so we use the integer conversions;
     if/when we add other arithmetic values,
     we will generalize this to arithmetic conversions.")
   (xdoc::p
    "This function never returns error:
     the usual arithmetic converesions always work.
     To show this, we need to show that @(tsee convert-integer-value)
     never returns errors when used to promote values,
     which we do via rules about @(tsee convert-integer-value)."))
  (b* ((type (uaconvert-types (type-of-value val1) (type-of-value val2)))
       (new-val1 (convert-integer-value val1 type))
       (new-val2 (convert-integer-value val2 type)))
    (mv (value-fix new-val1)
        (value-fix new-val2)))
  :guard-hints (("Goal" :in-theory (enable uaconvert-values-not-error-lemma
                                           value-arithmeticp
                                           value-realp)))

  :prepwork
  ((defruled uaconvert-values-not-error-lemma
     (implies (and (value-arithmeticp val)
                   (type-arithmeticp type))
              (and (valuep
                    (convert-integer-value val
                                           (uaconvert-types (type-of-value val)
                                                            type)))
                   (valuep
                    (convert-integer-value val
                                           (uaconvert-types type
                                                            (type-of-value val))))))
     :enable (uaconvert-types
              promote-type
              value-arithmeticp
              value-realp
              value-integerp
              value-unsigned-integerp
              value-signed-integerp
              type-arithmeticp
              type-realp
              type-integerp
              type-unsigned-integerp
              type-signed-integerp
              convert-integer-value-to-type-of-value
              valuep-of-convert-integer-value-from-schar-to-sint
              valuep-of-convert-integer-value-from-schar-to-slong
              valuep-of-convert-integer-value-from-schar-to-sllong
              valuep-of-convert-integer-value-from-sshort-to-sint
              valuep-of-convert-integer-value-from-sshort-to-slong
              valuep-of-convert-integer-value-from-sshort-to-sllong
              valuep-of-convert-integer-value-from-sint-to-slong
              valuep-of-convert-integer-value-from-sint-to-sllong
              valuep-of-convert-integer-value-from-slong-to-sllong
              valuep-of-convert-integer-value-from-uchar-to-sint
              valuep-of-convert-integer-value-from-uchar-to-slong
              valuep-of-convert-integer-value-from-uchar-to-sllong
              valuep-of-convert-integer-value-from-ushort-to-sint
              valuep-of-convert-integer-value-from-ushort-to-slong
              valuep-of-convert-integer-value-from-ushort-to-sllong
              valuep-of-convert-integer-value-from-uint-to-slong
              valuep-of-convert-integer-value-from-uint-to-sllong
              valuep-of-convert-integer-value-from-ulong-to-sllong)
     :disable ((:e type-sint)
               (:e type-slong)
               (:e type-sllong))))

  :hooks (:fix)

  ///

  (defruled type-of-value-of-uaconvert-values
    (implies (and (value-arithmeticp val1)
                  (value-arithmeticp val2))
             (b* (((mv new-val1 new-val2) (uaconvert-values val1 val2))
                  (type (uaconvert-types (type-of-value val1)
                                         (type-of-value val2))))
               (and (equal (type-of-value new-val1) type)
                    (equal (type-of-value new-val2) type))))
    :enable (uaconvert-values-not-error-lemma
             not-errorp-when-valuep
             type-of-value-of-convert-integer-value
             value-arithmeticp
             value-realp))

  (defret value-arithmeticp-of-uaconvert-values
    (and (value-arithmeticp new-val1)
         (value-arithmeticp new-val2))
    :hyp (and (value-arithmeticp val1)
              (value-arithmeticp val2))
    :hints (("Goal" :in-theory (enable uaconvert-values-not-error-lemma
                                       not-errorp-when-valuep
                                       value-arithmeticp
                                       value-realp))))

  (defrule value-promoted-arithmeticp-of-uaconvert-values
    (b* (((mv newval1 newval2) (uaconvert-values val1 val2)))
      (implies (and (value-arithmeticp val1)
                    (value-arithmeticp val2))
               (and (value-promoted-arithmeticp newval1)
                    (value-promoted-arithmeticp newval2))))
    :enable (uaconvert-values-not-error-lemma
             not-errorp-when-valuep
             value-promoted-arithmeticp
             value-arithmeticp
             value-realp))

  (defret value-integerp-of-uaconvert-values
    (and (value-integerp new-val1)
         (value-integerp new-val2))
    :hyp (and (value-integerp val1)
              (value-integerp val2))
    :hints (("Goal" :in-theory (enable uaconvert-values-not-error-lemma
                                       not-errorp-when-valuep
                                       value-arithmeticp
                                       value-realp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define result-integer-value ((mathint integerp) (type typep))
  :guard (type-nonchar-integerp type)
  :returns (val value-resultp)
  :short "Calculate the integer value result of an operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to most (but not all) integer operations,
     and thus it is factored in this ACL2 function.")
   (xdoc::p
    "Operations on unsigned integers are always well-defined,
     because if the exact mathematical result does not fit in the type,
     it is reduced modulo one plus the maximum integer of the type
     [C17:6.2.5/9].
     In contrast, operations on signed integers are not necessarily well-defined
     when the exact mathematical result does not fit in the type [C17:6.5/5].
     [C17] could be clearer on this point,
     but it seems that it allows implementations that silently wrap around
     as well as implementations that trap on overflow,
     as suggested by the example in [C17:5.1.2.3//15],
     as well as by the wording in [C17:H.2.2/1].
     Note also that [C17:3.4.3] says that integer overflow is
     an example of undefined behavior,
     but this should be taken to mean signed integer overflow,
     given that [C17:6.2.5/9] says that unsigned operations do not overflow
     (due to the modular reduction mentioned above).
     So for now we regard as an error
     the situation of a signed result that does not fit in the type,
     given that [C17] does not prescribe what should happen in this case;
     in the future, we may extend our model with a parameterization
     over the specifics of how this situation is handled.")
   (xdoc::p
    "We define most of the integer operations to
     obtain the mathematical integers from the operands,
     combine them according to the specifics of the operation,
     and then turning the resulting mathematical integer into an integer value.
     This ACL2 function serves to accomplish the last step.
     The type of the result,
     which is also the type of the operand(s)
     (after the usual arithmetic conversions [C17:6.3.1.8] for binary operations),
     is passed as argument to this ACL2 function,
     along with the mathematical integer of the result.
     We return a value or an error,
     according to the criteria explained above.")
   (xdoc::p
    "Note that this is the same calculation
     done in @(tsee convert-integer-value)
     after obtaining the mathematical integer from the starting value.
     So we could use this function
     in the definition of @(tsee convert-integer-value),
     but we prefer to keep them separate because
     in the future we may parameterize our C dynamic semantics
     on the choice of whether overflowing signed arithmetic
     should be an error (as it is now)
     or silently wrap around,
     or cause a trap (traps may have to be modeled explicitly).
     Since integer conversions are described separately
     from other integer operations in [C17],
     the behavior of integer conversions and other integer operations
     could be parameterized differently."))
  (b* ((mathint (ifix mathint)))
    (cond ((type-unsigned-integerp type)
           (value-integer (mod mathint (1+ (integer-type-max type)))
                          type))
          ((integer-type-rangep mathint type) (value-integer mathint type))
          (t (error (list :out-of-range mathint (type-fix type))))))
  :guard-hints (("Goal" :in-theory (enable integer-type-rangep ifix)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-result-integer-value
    (implies (not (errorp val))
             (equal (type-of-value val)
                    (type-fix type)))
    :hyp (type-nonchar-integerp type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plus-integer-value ((val valuep))
  :guard (and (value-integerp val)
              (value-promoted-arithmeticp val))
  :returns (resval valuep)
  :short "Apply unary @('+') to an integer value [C17:6.5.3.3/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the value has been already promoted,
     so we put that restriction in the guard.")
   (xdoc::p
    "Since the value is already promoted,
     this function returns the value unchanged.
     We introduce this function mainly for uniformity with other operations,
     despite it being trivial in a way."))
  (value-fix val)
  :hooks (:fix)

  ///

  (defret type-of-value-of-plus-integer-value
    (equal (type-of-value resval)
           (type-of-value val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minus-integer-value ((val valuep))
  :guard (and (value-integerp val)
              (value-promoted-arithmeticp val))
  :returns (resval value-resultp)
  :short "Apply unary @('-') to an integer value [C17:6.5.3.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the value has been already promoted,
     so we put that restriction in the guard.")
   (xdoc::p
    "The type of the result is the (promoted) type of the operand [C17:6.5.3.3/3],
     so it is the same type as the input value of this ACL2 function.
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function."))
  (b* ((mathint (value-integer->get val))
       (result (- mathint))
       (resval (result-integer-value result (type-of-value val)))
       ((when (errorp resval)) (error (list :undefined-minus (value-fix val)))))
    resval)
  :hooks (:fix)

  ///

  (defret type-of-value-of-minus-integer-value
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (type-of-value val)))
    :hyp (value-integerp val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitnot-integer-value ((val valuep))
  :guard (and (value-integerp val)
              (value-promoted-arithmeticp val))
  :returns (resval value-resultp)
  :short "Apply @('~') to an integer value [C17:6.5.3.3/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the value has been already promoted,
     so we put that restriction in the guard.")
   (xdoc::p
    "The result is obtained by complementing each bit of the operand
     [C17:6.5.3.3/4].
     Thus, the result must have the same type as the operand.")
   (xdoc::p
    "We calculate the result
     via @(tsee lognot) followed by @(tsee result-integer-value),
     which works for both signed and unsigned operands,
     as explained below.")
   (xdoc::p
    "For a signed integer of @('n') bits,
     the result of @(tsee lognot) is a signed integer of @('n') bits:
     i.e. the following is a theorem")
   (xdoc::codeblock
    "(implies (signed-byte-p n x)"
    "         (signed-byte-p n (lognot x)))")
   (xdoc::p
    "which can be proved, for example,
     by including community book @('kestrel/arithmetic-light/expt.lisp').")
   (xdoc::p
    "Thus, applying @(tsee result-integer-value) never yields an error
     when applied to the result @(tsee lognot),
     and just wraps the ACL2 integer into a C integer of the appropriate type.")
   (xdoc::p
    "For an unsigned integer of @('n') bits,
     @(tsee lognot) returns a negative result (of @('n') bits)
     if the high (i.e. sign) bit of the operand is set.
     In this case, to fit into the range of an unsigned C integer,
     we need to turn the negative integer
     into the non-negative one that has the same low @('n') bits,
     and @(tsee result-integer-value) does that;
     note that @(tsee mod) is equivalent to @(tsee acl2::loghead),
     as can be seen in the definition of the latter.")
   (xdoc::p
    "Because the result of the signed operation is always in range,
     and the unsigned operation never causes errors in general,
     this operation never causes errors.
     So we prove an additional theorems saying that
     this operation always returns a value (never an error).
     But we need a hypothesis implied by the guard for this to hold.
     We keep the @(':returns') type broader (i.e. @(tsee value-resultp))
     but unconditional, for consistency with other operations."))
  (b* ((mathint (value-integer->get val))
       (result (lognot mathint))
       (resval (result-integer-value result (type-of-value val))))
    resval)
  :hooks (:fix)

  ///

  (defret valuep-of-bitnot-integer-value
    (valuep resval)
    :hyp (value-integerp val)
    :hints (("Goal" :in-theory (enable result-integer-value
                                       integer-type-rangep
                                       integer-type-max
                                       integer-type-min
                                       lognot
                                       value-integerp
                                       value-unsigned-integerp
                                       value-signed-integerp
                                       value-integer->get
                                       (:e schar-min)
                                       (:e schar-max)
                                       (:e sshort-min)
                                       (:e sshort-max)
                                       (:e sint-min)
                                       (:e sint-max)
                                       (:e slong-min)
                                       (:e slong-max)
                                       (:e sllong-min)
                                       (:e sllong-max)
                                       ifix))))

  (defret type-of-value-of-bitnot-integer-value
    (equal (type-of-value resval)
           (type-of-value val))
    :hyp (value-integerp val)
    :hints (("Goal" :in-theory (enable result-integer-value
                                       integer-type-rangep
                                       integer-type-max
                                       integer-type-min
                                       lognot
                                       value-integerp
                                       value-unsigned-integerp
                                       value-signed-integerp
                                       value-integer->get
                                       (:e schar-min)
                                       (:e schar-max)
                                       (:e sshort-min)
                                       (:e sshort-max)
                                       (:e sint-min)
                                       (:e sint-max)
                                       (:e slong-min)
                                       (:e slong-max)
                                       (:e sllong-min)
                                       (:e sllong-max)
                                       ifix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-integer-value ((val valuep))
  :guard (value-integerp val)
  :returns (resval valuep)
  :short "Apply @('!') to an integer value [C17:6.5.3.3/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This always returns an @('int') (never an error), either 0 or 1.
     It is equivalent to comparing the integer for equality to 0,
     which in our curren model is equivalent to
     whether the integer value is 0 or not."))
  (if (equal (value-integer->get val) 0)
      (value-sint 1)
    (value-sint 0))
  :hooks (:fix)

  ///

  (defret type-of-value-of-lognot-integer-value
    (equal (type-of-value resval)
           (type-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mul-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval value-resultp)
  :short "Apply binary @('*') to integer values [C17:6.5.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       (result (* mathint1 mathint2))
       (resval (result-integer-value result (type-of-value val1)))
       ((when (errorp resval)) (error (list :undefined-mul
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define div-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval value-resultp)
  :short "Apply @('/') to integer values [C17:6.5.5/5] [C17:6.5.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function.")
   (xdoc::p
    "It is an error if the divisor is 0 [C17:6.5.5/5].")
   (xdoc::p
    "We use @(tsee truncate) because C integer division
     truncates towards zero [C17:6.5.5/6]."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       ((when (equal mathint2 0)) (error :division-by-zero))
       (result (truncate mathint1 mathint2))
       (resval (result-integer-value result (type-of-value val1)))
       ((when (errorp resval)) (error (list :undefined-div
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rem-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval value-resultp)
  :short "Apply @('%') to integer values [C17:6.5.5/5] [C17:6.5.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function.")
   (xdoc::p
    "It is an error if the divisor is 0 [C17:6.5.5/5].")
   (xdoc::p
    "We use @(tsee rem) because it matches the use of @(tsee truncate),
     in terms of the relationship between quotient and remainder [C17:6.5.5/6],
     in the definition of @('/') in @(tsee rem-integer-values)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       ((when (equal mathint2 0)) (error :division-by-zero))
       (result (rem mathint1 mathint2))
       (resval (result-integer-value result (type-of-value val1)))
       ((when (errorp resval)) (error (list :undefined-rem
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :guard-hints (("Goal" :in-theory (enable rem)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval value-resultp)
  :short "Apply binary @('+') to integer values [C17:6.5.6/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       (result (+ mathint1 mathint2))
       (resval (result-integer-value result (type-of-value val1)))
       ((when (errorp resval)) (error (list :undefined-add
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sub-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval value-resultp)
  :short "Apply binary @('-') to integer values [C17:6.5.6/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       (result (- mathint1 mathint2))
       (resval (result-integer-value result (type-of-value val1)))
       ((when (errorp resval)) (error (list :undefined-sub
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shl-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply @('<<') to integer values [C17:6.5.7/3] [C17:6.5.7/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the arithmetic promotions.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the left operand [C17:6.5.7/3].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function.
     The left operand must be non-negative,
     otherwise it is an error.
     The right operand must be non-negative
     and below the number of bits of the left operand,
     otherwise it is an error."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       (type1 (type-of-value val1))
       ((unless (<= 0 mathint1))
        (error (list :undefined-shl
                     (value-fix val1)
                     (value-fix val2))))
       ((unless (integer-range-p 0 (integer-type-bits type1) mathint2))
        (error (list :undefined-shl
                     (value-fix val1)
                     (value-fix val2))))
       (result (* mathint1 (expt 2 mathint2)))
       (resval (result-integer-value result type1))
       ((when (errorp resval)) (error (list :undefined-shl
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :guard-hints (("Goal" :in-theory (enable integer-range-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shr-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply @('>>') to integer values [C17:6.5.7/3] [C17:6.5.7/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the arithmetic promotions.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the left operand [C17:6.5.7/3].
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function.
     The left operand must be non-negative,
     otherwise it is an error.
     The right operand must be non-negative
     and below the number of bits of the left operand,
     otherwise it is an error."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2))
       (type1 (type-of-value val1))
       ((unless (<= 0 mathint1))
        (error (list :undefined-shr
                     (value-fix val1)
                     (value-fix val2))))
       ((unless (integer-range-p 0 (integer-type-bits type1) mathint2))
        (error (list :undefined-shr
                     (value-fix val1)
                     (value-fix val2))))
       (result (truncate mathint1 (expt 2 mathint2)))
       (resval (result-integer-value result type1))
       ((when (errorp resval)) (error (list :undefined-shr
                                            (value-fix val1)
                                            (value-fix val2)))))
    resval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lt-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('<') to integer values [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is always @('int').
     This operation is always well-defined,
     so it always returns a value (never an error)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (if (< mathint1 mathint2)
        (value-sint 1)
      (value-sint 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gt-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('>') to integer values [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is always @('int').
     This operation is always well-defined,
     so it always returns a value (never an error)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (if (> mathint1 mathint2)
        (value-sint 1)
      (value-sint 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define le-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('<=') to integer values [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is always @('int').
     This operation is always well-defined,
     so it always returns a value (never an error)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (if (<= mathint1 mathint2)
        (value-sint 1)
      (value-sint 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ge-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('>=') to integer values [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is always @('int').
     This operation is always well-defined,
     so it always returns a value (never an error)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (if (>= mathint1 mathint2)
        (value-sint 1)
      (value-sint 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eq-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('==') to integer values [C17:6.5.9/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is always @('int').
     This operation is always well-defined,
     so it always returns a value (never an error)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (if (= mathint1 mathint2)
        (value-sint 1)
      (value-sint 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ne-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('!=') to integer values [C17:6.5.9/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is always @('int').
     This operation is always well-defined,
     so it always returns a value (never an error)."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (if (/= mathint1 mathint2)
        (value-sint 1)
      (value-sint 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitand-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('&') to integer values [C17:6.5.10/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     This operation is always well-defined,
     so it always returns a value (never an error).")
   (xdoc::p
    "Verifying the guards of this function involves showing that
     @(tsee logand) is in the range of an integer type
     when its operands are in the range of the same integer type.
     we use rules to rewrite @(tsee integer-type-rangep)
     to @(tsee signed-byte-p) and @(tsee unsigned-byte-p),
     so that library rules apply about
     @(tsee logand) returning @(tsee signed-byte-p) or @(tsee unsigned-byte-p)
     under suitable conditions.
     To relieve the hypotheses of these library rules,
     we enable the rules about the accessors of the integer values.
     The @(':use') hint server to exclude the cases in which
     the two values have different kinds,
     which is impossible because the two values have the same type."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (value-integer (logand mathint1 mathint2) (type-of-value val1)))
  :guard-hints (("Goal"
                 :in-theory (e/d (integer-type-rangep-to-signed-byte-p
                                  integer-type-rangep-to-unsigned-byte-p
                                  integer-type-bits
                                  value-promoted-arithmeticp
                                  value-arithmeticp
                                  value-realp
                                  value-integerp
                                  value-unsigned-integerp
                                  value-signed-integerp
                                  value-integer->get
                                  signed-byte-p-of-value-sint->get
                                  signed-byte-p-of-value-slong->get
                                  signed-byte-p-of-value-sllong->get
                                  unsigned-byte-p-of-value-uint->get
                                  unsigned-byte-p-of-value-ulong->get
                                  unsigned-byte-p-of-value-ullong->get)
                                 (signed-byte-p
                                  unsigned-byte-p
                                  type-kind-of-type-of-value))
                 :use ((:instance type-kind-of-type-of-value (val val1))
                       (:instance type-kind-of-type-of-value (val val2)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitxor-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('^') to integer values [C17:6.5.11/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     This operation is always well-defined,
     so it always returns a value (never an error).")
   (xdoc::p
    "The guard verification of this function
     is similar to @(tsee bitand-integer-values);
     see that function documentation for details on this."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (value-integer (logxor mathint1 mathint2) (type-of-value val1)))
  :guard-hints (("Goal"
                 :in-theory (e/d (integer-type-rangep-to-signed-byte-p
                                  integer-type-rangep-to-unsigned-byte-p
                                  integer-type-bits
                                  value-promoted-arithmeticp
                                  value-arithmeticp
                                  value-realp
                                  value-integerp
                                  value-unsigned-integerp
                                  value-signed-integerp
                                  value-integer->get
                                  signed-byte-p-of-value-sint->get
                                  signed-byte-p-of-value-slong->get
                                  signed-byte-p-of-value-sllong->get
                                  unsigned-byte-p-of-value-uint->get
                                  unsigned-byte-p-of-value-ulong->get
                                  unsigned-byte-p-of-value-ullong->get)
                                 (signed-byte-p
                                  unsigned-byte-p
                                  type-kind-of-type-of-value))
                 :use ((:instance type-kind-of-type-of-value (val val1))
                       (:instance type-kind-of-type-of-value (val val2)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitior-integer-values ((val1 valuep) (val2 valuep))
  :guard (and (value-integerp val1)
              (value-integerp val2)
              (value-promoted-arithmeticp val1)
              (value-promoted-arithmeticp val2)
              (equal (type-of-value val1)
                     (type-of-value val2)))
  :returns (resval valuep)
  :short "Apply @('|') to integer values [C17:6.5.12/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the values have already been subjected to the usual arithmetic conversions,
     so they are promoted arithmetic value with the same type.
     We put this condition in the guard.")
   (xdoc::p
    "The type of the result is the same as the operands [C17:6.3.1.8/1].
     This operation is always well-defined,
     so it always returns a value (never an error).")
   (xdoc::p
    "The guard verification of this function
     is similar to @(tsee bitand-integer-values);
     see that function documentation for details on this."))
  (b* ((mathint1 (value-integer->get val1))
       (mathint2 (value-integer->get val2)))
    (value-integer (logior mathint1 mathint2) (type-of-value val1)))
  :guard-hints (("Goal"
                 :in-theory (e/d (integer-type-rangep-to-signed-byte-p
                                  integer-type-rangep-to-unsigned-byte-p
                                  integer-type-bits
                                  value-promoted-arithmeticp
                                  value-arithmeticp
                                  value-realp
                                  value-integerp
                                  value-unsigned-integerp
                                  value-signed-integerp
                                  value-integer->get
                                  signed-byte-p-of-value-sint->get
                                  signed-byte-p-of-value-slong->get
                                  signed-byte-p-of-value-sllong->get
                                  unsigned-byte-p-of-value-uint->get
                                  unsigned-byte-p-of-value-ulong->get
                                  unsigned-byte-p-of-value-ullong->get)
                                 (signed-byte-p
                                  unsigned-byte-p
                                  type-kind-of-type-of-value))
                 :use ((:instance type-kind-of-type-of-value (val val1))
                       (:instance type-kind-of-type-of-value (val val2)))))
  :hooks (:fix))
