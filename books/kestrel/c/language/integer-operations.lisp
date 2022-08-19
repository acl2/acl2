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

(define value-integer ((int integerp) (type typep))
  :guard (type-integerp type)
  :returns (val value-resultp)
  :short "Turn a mathematical (i.e. ACL2) integer into a C integer value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the C integer value is passed as parameter to this function.")
   (xdoc::p
    "If the type is plain @('char'), we return an error for now,
     because our model of values does not yet include plain @('char').")
   (xdoc::p
    "If the integer is not in the range representable by the type,
     we return an error."))
  (b* ((int (ifix int)))
    (type-case type
               :void (error (impossible))
               :char (error :char-not-supported)
               :uchar (if (uchar-integerp int)
                          (value-uchar int)
                        (error (list :uchar-out-of-range int)))
               :schar (if (schar-integerp int)
                          (value-schar int)
                        (error (list :schar-out-of-range int)))
               :ushort (if (ushort-integerp int)
                           (value-ushort int)
                         (error (list :ushort-out-of-range int)))
               :sshort (if (sshort-integerp int)
                           (value-sshort int)
                         (error (list :sshort-out-of-range int)))
               :uint (if (uint-integerp int)
                         (value-uint int)
                       (error (list :uint-out-of-range int)))
               :sint (if (sint-integerp int)
                         (value-sint int)
                       (error (list :sint-out-of-range int)))
               :ulong (if (ulong-integerp int)
                          (value-ulong int)
                        (error (list :ulong-out-of-range int)))
               :slong (if (slong-integerp int)
                          (value-slong int)
                        (error (list :slong-out-of-range int)))
               :ullong (if (ullong-integerp int)
                           (value-ullong int)
                         (error (list :ullong-out-of-range int)))
               :sllong (if (sllong-integerp int)
                           (value-sllong int)
                         (error (list :sllong-out-of-range int)))
               :pointer (error (impossible))
               :struct (error (impossible))
               :array (error (impossible))))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp)))
  :hooks (:fix)
  ///

  (defret type-of-value-of-value-integer
    (implies (not (errorp val))
             (equal (type-of-value val)
                    (type-fix type)))
    :hints (("Goal" :in-theory (enable type-of-value))))

  (defret value-integerp-of-value-integer
    (implies (not (errorp val))
             (value-integerp val))
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
    (b* ((val (value-integer int type)))
      (implies (not (errorp val))
               (equal (value-integer->get val)
                      (ifix int))))
    :enable (value-integer
             value-integer->get)))

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
    (if (type-unsigned-integerp type)
        (value-integer (mod mathint (1+ (integer-type-max type)))
                       type)
      (value-integer mathint type)))
  :hooks (:fix)
  ///

  (local (include-book "kestrel/arithmetic-light/mod" :dir :system))

  (defret type-of-value-of-convert-integer-value
    (implies (not (errorp newval))
             (equal (type-of-value newval)
                    (type-fix type))))

  (local
   (defret value-kind-of-convert-integer-value-lemma
     (implies (not (errorp newval))
              (equal (value-kind newval)
                     (type-kind type)))
     :hyp (typep type)
     :rule-classes nil
     :hints (("Goal"
              :use type-of-value-of-convert-integer-value
              :in-theory (disable type-of-value-of-convert-integer-value
                                  convert-integer-value)))))

  (defret value-kind-of-convert-integer-value
    (implies (not (errorp newval))
             (equal (value-kind newval)
                    (type-kind type)))
    :hints (("Goal" :use (:instance value-kind-of-convert-integer-value-lemma
                                    (type (type-fix type))))))

  (defret value-integerp-of-convert-integer-value
    (implies (not (errorp newval))
             (value-integerp newval)))

  (defruled convert-integer-value-to-type-of-value
    (implies (and (value-integerp val)
                  (equal type (type-of-value val)))
             (equal (convert-integer-value val type)
                    (value-fix val)))
    :enable (value-integerp
             value-signed-integerp
             value-unsigned-integerp
             integer-type-max
             value-integer->get
             value-integer))

  (defruled valuep-of-convert-integer-value-to-unsigned
    (implies (type-unsigned-integerp type)
             (valuep (convert-integer-value val type)))
    :enable (convert-integer-value
             value-integer
             type-unsigned-integerp
             integer-type-max
             uchar-integerp-alt-def
             ushort-integerp-alt-def
             uint-integerp-alt-def
             ulong-integerp-alt-def
             ullong-integerp-alt-def))

  (defruled valuep-of-convert-integer-value-from-schar-to-sint
    (implies (value-case val :schar)
             (valuep (convert-integer-value val (type-sint))))
    :enable (value-integer
             value-integer->get
             sint-integerp-alt-def))

  (defruled valuep-of-convert-integer-value-from-sshort-to-sint
    (implies (value-case val :sshort)
             (valuep (convert-integer-value val (type-sint))))
    :enable (value-integer
             value-integer->get
             sint-integerp-alt-def))

  (defruled valuep-of-convert-integer-value-from-uchar-to-sint
    (implies (and (value-case val :uchar)
                  (<= (uchar-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (value-integer
             value-integer->get
             sint-integerp-alt-def))

  (defruled valuep-of-convert-integer-value-from-ushort-to-sint
    (implies (and (value-case val :ushort)
                  (<= (ushort-max) (sint-max)))
             (valuep (convert-integer-value val (type-sint))))
    :enable (value-integer
             value-integer->get
             sint-integerp-alt-def)))

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
                          value-unsigned-integerp)
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
                          value-unsigned-integerp)
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
