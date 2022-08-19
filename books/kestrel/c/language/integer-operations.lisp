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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-operations
  :parents (language)
  :short "Operations on C integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The following remarks apply to intger operations in general
     (not to all of them, but to most of them),
     and are thus factored here instead of being repeated
     in the documentation for all the operations to which the remarks apply.
     Operations on unsigned integers are always well-defined,
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
     over the specifics of how this situation is handled."))
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
              :pointer (prog2$ (impossible) 0)
              :array (prog2$ (impossible) 0)
              :struct (prog2$ (impossible) 0))
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
    :enable (value-integer->get
             integer-type-min
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
      (t (prog2$ (impossible) (ec-call (value-uchar :irrelevant))))))
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

  (defret type-of-value-of-value-integer
    (equal (type-of-value val)
           (type-fix type))
    :hyp (type-nonchar-integerp type)
    :hints (("Goal" :in-theory (enable type-of-value
                                       type-nonchar-integerp))))

  (defret value-kind-of-value-integer
    (equal (value-kind val)
           (type-kind type))
    :hyp (type-nonchar-integerp type)
    :hints (("Goal" :in-theory (enable type-nonchar-integerp))))

  (defret value-integerp-of-value-integer
    (value-integerp val)
    :hints (("Goal" :in-theory (enable value-integerp
                                       value-signed-integerp
                                       value-unsigned-integerp)))))

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
             uchar-integer-fix
             schar-integer-fix
             ushort-integer-fix
             sshort-integer-fix
             uint-integer-fix
             sint-integer-fix
             ulong-integer-fix
             slong-integer-fix
             ullong-integer-fix
             sllong-integer-fix
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
  :prepwork ((local (include-book "kestrel/arithmetic-light/mod" :dir :system)))
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
             (value-integerp newval)))

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

  (defruled valuep-of-convert-integer-value-from-sshort-to-sint
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-sint))))
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

  (defruled valuep-of-convert-integer-value-from-ushort-to-sint
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define promote-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (promoted-val
            valuep
            :hints
            (("Goal"
              :cases ((equal (promote-type (type-of-value val))
                             (type-of-value val)))
              :in-theory (e/d
                          (promote-type
                           convert-integer-value-to-type-of-value
                           valuep-of-convert-integer-value-to-unsigned
                           valuep-of-convert-integer-value-from-schar-to-sint
                           valuep-of-convert-integer-value-from-sshort-to-sint
                           valuep-of-convert-integer-value-from-uchar-to-sint
                           valuep-of-convert-integer-value-from-ushort-to-sint)
                          ((:e type-sint))))))
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
     we convert the value to the promoted type.")
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
  :hooks (:fix)
  ///

  (defrule value-integerp-of-promote-value
    (equal (value-integerp (promote-value val))
           (value-integerp (value-fix val)))
    :hints (("Goal"
             :in-theory (e/d
                         (promote-type
                          convert-integer-value-to-type-of-value
                          valuep-of-convert-integer-value-to-unsigned
                          valuep-of-convert-integer-value-from-schar-to-sint
                          valuep-of-convert-integer-value-from-sshort-to-sint
                          valuep-of-convert-integer-value-from-uchar-to-sint
                          valuep-of-convert-integer-value-from-ushort-to-sint
                          not-errorp-when-valuep)
                         ((:e type-sint))))))

  (defruled type-of-value-of-promote-value
    (equal (type-of-value (promote-value val))
           (promote-type (type-of-value val)))
    :hints (("Goal"
             :in-theory (e/d
                         (promote-type
                          convert-integer-value-to-type-of-value
                          valuep-of-convert-integer-value-to-unsigned
                          valuep-of-convert-integer-value-from-schar-to-sint
                          valuep-of-convert-integer-value-from-sshort-to-sint
                          valuep-of-convert-integer-value-from-uchar-to-sint
                          valuep-of-convert-integer-value-from-ushort-to-sint
                          not-errorp-when-valuep
                          value-integerp
                          value-signed-integerp
                          value-unsigned-integerp
                          type-nonchar-integerp)
                         ((:e type-sint))))))

  (defret value-promoted-arithmeticp-of-promote-value
    (value-promoted-arithmeticp promoted-val)
    :hyp (value-arithmeticp val)
    :hints (("Goal"
             :in-theory (e/d
                         (promote-type
                          convert-integer-value-to-type-of-value
                          valuep-of-convert-integer-value-to-unsigned
                          valuep-of-convert-integer-value-from-schar-to-sint
                          valuep-of-convert-integer-value-from-sshort-to-sint
                          valuep-of-convert-integer-value-from-uchar-to-sint
                          valuep-of-convert-integer-value-from-ushort-to-sint
                          not-errorp-when-valuep
                          value-promoted-arithmeticp
                          value-arithmeticp
                          value-realp
                          value-integerp
                          value-signed-integerp
                          value-unsigned-integerp
                          type-nonchar-integerp)
                         ((:e type-sint)))))))

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
