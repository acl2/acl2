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

(include-book "values")
(include-book "static-semantics")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-operations
  :parents (language)
  :short "Operations on C integers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer->get ((val valuep))
  :guard (value-integerp val)
  :returns (int integerp)
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
             value-signed-integerp))

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

(define convert-integer-value ((val valuep) (type typep))
  :guard (and (value-integerp val)
              (type-nonchar-integerp type))
  :returns (newval value-resultp)
  :short "Convert an integer value to an integer type [C:6.3.1.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We extract the underlying mathematical (i.e. ACL2) integer from the value,
     and we attempt to contruct an integer value of the new type from it.
     If the new type is unsigned,
     the mathematical integer is reduced
     modulo one plus the maximum value of the unsigned type [C:6.3.1.3/2];
     this always works, i.e. no error is ever returned.
     If the new type is signed, there are two cases [C:6.3.1.3/3]:
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
  :guard-hints (("Goal" :in-theory (enable integer-type-rangep)))
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
             integer-type-max))

  (defruled valuep-of-convert-integer-value-to-unsigned
    (implies (type-unsigned-integerp type)
             (valuep (convert-integer-value val type))))

  (defruled valuep-of-convert-integer-value-from-schar-to-sint
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-sint))))
    :disable ((:e type-sint))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-schar-to-slong
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-schar-to-sllong
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-sshort-to-sint
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-sshort-to-slong
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-sshort-to-sllong
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-sint-to-slong
    (implies (value-case val :sint)
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-sint-to-sllong
    (implies (value-case val :sint)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-slong-to-sllong
    (implies (value-case val :slong)
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-uchar-to-sint
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-uchar-to-slong
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (slong-max)))
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-uchar-to-sllong
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-ushort-to-sint
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-ushort-to-slong
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (slong-max)))
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-ushort-to-sllong
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-uint-to-slong
    (implies (and (value-case val :uint)
                  (<= (uint-max) (slong-max)))
             (valuep (convert-integer-value val (type-slong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max))

  (defruled valuep-of-convert-integer-value-from-uint-to-sllong
    (implies (and (value-case val :uint)
                  (<= (uint-max) (sllong-max)))
             (valuep (convert-integer-value val (type-sllong))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define promote-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (promoted-val valuep
                         :hints
                         (("Goal"
                           :in-theory
                           (enable promote-value-not-error-lemma))))
  :short "Apply the integer promotions to a value [C:6.3.1.1/2]."
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
          [C:6.3.1.8]."
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
              valuep-of-convert-integer-value-from-uint-to-sllong)
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
     [C:6.2.5/9].
     In contrast, operations on signed integers are not necessarily well-defined
     when the exact mathematical result does not fit in the type [C:6.5/5].
     [C] could be clearer on this point,
     but it seems that it allows implementations that silently wrap around
     as well as implementations that trap on overflow,
     as suggested by the example in [C:5.1.2.3//15],
     as well as by the wording in [C:H.2.2/1].
     Note also that [C:3.4.3] says that integer overflow is
     an example of undefined behavior,
     but this should be taken to mean signed integer overflow,
     given that [C:6.2.5/9] says that unsigned operations do not overflow
     (due to the modular reduction mentioned above).
     So for now we regard as an error
     the situation of a signed result that does not fit in the type,
     given that [C] does not prescribe what should happen in this case;
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
     (after the usual arithmetic conversions [C:6.3.1.8] for binary operations),
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
     from other integer operations in [C],
     the behavior of integer conversions and other integer operations
     could be parameterized differently."))
  (b* ((mathint (ifix mathint)))
    (cond ((type-unsigned-integerp type)
           (value-integer (mod mathint (1+ (integer-type-max type)))
                          type))
          ((integer-type-rangep mathint type) (value-integer mathint type))
          (t (error (list :out-of-range mathint (type-fix type))))))
  :guard-hints (("Goal" :in-theory (enable integer-type-rangep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plus-integer-value ((val valuep))
  :guard (and (value-integerp val)
              (value-promoted-arithmeticp val))
  :returns (resval value-resultp)
  :short "Apply unary @('+') to an integer value [C:6.5.3.3/2]."
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minus-integer-value ((val valuep))
  :guard (and (value-integerp val)
              (value-promoted-arithmeticp val))
  :returns (resval value-resultp)
  :short "Apply unary @('-') to an integer value [C:6.5.3.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the value has been already promoted,
     so we put that restriction in the guard.")
   (xdoc::p
    "The type of the result is the (promoted) type of the operand [C:6.5.3.3/3],
     so it is the same type as the input value of this ACL2 function.
     We use @(tsee result-integer-value) to return the resulting value,
     or an error, as documented in that function."))
  (b* ((mathint (value-integer->get val))
       (result (- mathint))
       (resval (result-integer-value result (type-of-value val)))
       ((when (errorp resval)) (error (list :undefined-minus (value-fix val)))))
    resval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitnot-integer-value ((val valuep))
  :guard (and (value-integerp val)
              (value-promoted-arithmeticp val))
  :returns (resval value-resultp)
  :short "Apply @('~') to an integer value [C:6.5.3.3/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "By the time we reach this ACL2 function,
     the value has been already promoted,
     so we put that restriction in the guard.")
   (xdoc::p
    "The result is obtained by complementing each bit of the operand
     [C:6.5.3.3/4].
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
     by including @('[books]/kestrel/arithmetic-light/expt.lisp').")
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
     So we prove an additional theorem saying that
     this operation always returns a value.
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
                                       (:e sllong-max))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-integer-value ((val valuep))
  :guard (value-integerp val)
  :returns (resval valuep)
  :short "Apply @('!') to an integer value [C:6.5.3.3/5]."
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
  :hooks (:fix))

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
