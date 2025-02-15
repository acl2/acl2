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

(include-book "centaur/fty/top" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation-environments
  :parents (language)
  :short "Implementation environments for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some aspects of the syntax and semantics of C are implementation-dependent.
     [C17:5] introduces the notion of translation and execution environments,
     which specify those aspects.
     In our formalization, we introduce a notion of implementation environment,
     which puts together the translation and execution environments in [C17].
     That is, an implementation environment
     specifies the implementation-dependent aspects of C.
     We prefer to formalize one (implementation) environment,
     instead of two (translation and execution) environments,
     because the latter two share several aspects (e.g. integer sizes),
     and therefore it seems simpler to have one notion.")
   (xdoc::p
    "We start by capturing some aspects of the C implementation environment.
     More will be added in the future.")
   (xdoc::p
    "Initially, our formalization of implementation environments
     is not used in other parts of the C formalization;
     furthermore, it captures notions already captured elsewhere,
     such as the "
    (xdoc::seetopic "integer-formats" "integer formats")
    ". But we plan to update the rest of the formalization to use this,
     also removing those then-redundant parts."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uchar-format
  :short "Fixtype of formats of @('unsigned char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of the @('unsigned char') type are represented
     using a pure binary notation [C17:6.2.6.1/3],
     i.e. where each bit counts for a successive power of 2.
     Footnote 50 says that a byte consists of @('CHAR_BIT') bits,
     and implies that an @('unsigned char') consists of one byte
     (as also implied by [C17:6.5.3.4/2] and [C17:6.5.3.4/4]).")
   (xdoc::p
    "Thus, the format of @('unsigned char') objects is determined
     by their number of bits, i.e. @('CHAR_BIT').
     This is required to be at least 8 [C17:5.2.4.2.1/1]."))
  ((bits nat :reqfix (if (>= bits 8) bits 8)))
  :require (>= bits 8)
  :pred uchar-formatp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum signed-format
  :short "Fixtype of signed formats."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.2.6.2/2] lists three possible ways in which a sign bit equal to 1
     modifies the value of the integer value whose sign bit is 0.
     We call these `signed formats', even though [C17] does not use this term."))
  (:sign-magnitude ())
  (:ones-complement ())
  (:twos-complement ())
  :pred signed-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod schar-format
  :short "Fixtype of formats of @('signed char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of the @('signed char') type, like all the other values,
     must be represented as one or more bytes [ISO:6.2.6.1/4].
     Objects of the @('signed char') type,
     like all other signed integer objects,
     must have no more value bits
     than value bits of their unsigned counterpart
     [ISO:6.2.6.2/2],
     i.e. @('unsigned char') objects in this case,
     which consist of exactly one byte (see @(tsee uchar-format)):
     therefore, @('signed char') objects must take exactly one byte as well.")
   (xdoc::p
    "Since @('signed char') objects must have one sign bit and no padding bits
     [ISO:6.2.6.2/2],
     they must have exactly @($\\mathtt{CHAR\\_BIT} - 1$) value bits.
     Since the values of the value bits of a signed integer type
     must be equal to the value bits of the unsigned integer type counterpart
     [ISO:6.2.6.2/2],
     the value bits of @('signed char') values are the low bits of the byte,
     and the sign is the high bit.")
   (xdoc::p
    "While the byte/bit format of @('signed char') is thus set,
     the exact values represented by this byte/bit format depend on the "
    (xdoc::seetopic "signed-format" "signed format")
    " (when the sign bit is 1).
     Furthermore, [ISO:6.2.6.2/2] identifies one specific bit pattern,
     for each signed format,
     as a possible trap representation:
     it either is a trap representation or it is not.
     These two choices
     (i.e. the signed format,
     and whether the specific pattern is a trap representation),
     completely define the representation of @('signed char').")
   (xdoc::p
    "We formalize the format of @('signed char') as consisting of
     a specification of signed format
     and a boolean flag saying whether the aforementioned pattern is a trap."))
  ((signed signed-format)
   (trap bool))
  :pred schar-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char-format
  :short "Fixtype of formats of @('char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('char') type has the same representation as
     either @('unsigned char') or @('signed char')
     [C17:6.2.5/15].
     The choice is captured by a boolean."))
  ((signedp bool))
  :pred char-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum uinteger-bit-role
  :short "Fixtype of roles of integer bits in unsigned integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each bit in the object representation of unsigned integers [C17:6.2.6.2/1]
     is either a value bit (representing a power of 2) or a padding bit.
     This fixtype represents these choices,
     where the natural number in the @(':value') case
     is the exponent @($i$) of the power @($2^i$).")
   (xdoc::p
    "This is similar to @(tsee sinteger-bit-role),
     without the choice of a sign bit."))
  (:value ((exp nat)))
  (:padding ())
  :pred uinteger-bit-rolep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist uinteger-bit-role-list
  :short "Fixtype of lists of roles of integer bits in unsigned integers."
  :elt-type uinteger-bit-role
  :true-listp t
  :elementp-of-nil nil
  :pred uinteger-bit-role-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum sinteger-bit-role
  :short "Fixtype of roles of integer bits in signed integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each bit in the object representation of signed integers [C17:6.2.6.2/2]
     is either a value bit (representing a power of 2)
     or a padding bit
     or a sign bit.
     This fixtype represents these choices,
     where the natural number in the @(':value') case
     is the exponent @($i$) of the power @($2^i$).")
   (xdoc::p
    "This is similar to @(tsee uinteger-bit-role),
     with the added choice of a sign bit."))
  (:sign ())
  (:value ((exp nat)))
  (:padding ())
  :pred sinteger-bit-rolep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist sinteger-bit-role-list
  :short "Fixtype of lists of roles of integer bits in signed integers."
  :elt-type sinteger-bit-role
  :true-listp t
  :elementp-of-nil nil
  :pred sinteger-bit-role-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ienv
  :short "Fixtype of implementation environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this only contains a few components,
     but we plan to add more components.
     In particular, we plan to add components for
     the formats of other integer types,
     which will make use of
     @(tsee uinteger-bit-role) and @(tsee sinteger-bit-role)."))
  ((uchar-format uchar-format)
   (schar-format schar-format)
   (char-format char-format))
  :tag :ienv
  :pred ienvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-bits ((ienv ienvp))
  :returns (bits posp)
  :short "The ACL2 integer value of @('CHAR_BIT') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prefer to use dash instead of underscore,
     since it's more common convention in ACL2.
     We also prefer the plural `bits', since it's a number of bits."))
  (uchar-format->bits (ienv->uchar-format ienv))
  :hooks (:fix)
  ///

  (defret ienv->char-bits-type-prescription
    (and (posp bits)
         (> bits 1))
    :rule-classes :type-prescription)

  (defret ienv->char-bits-lower-bound
    (>= bits 8)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uchar-max ((ienv ienvp))
  :returns (max posp :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of @('UCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This directly derives from @('CHAR_BIT'),
     as discussed in @(tsee uchar-format),
     and in footnote 50 of [C17:6.2.6.1//3],
     which says that @('unsigned char') values
     range from 0 to @($2^{\\mathtt{CHAR\\_BIT}}-1$).")
   (xdoc::p
    "This is at least 255, as required by [C17:5.2.4.2.1/1]."))
  (1- (expt 2 (ienv->char-bits ienv)))
  :hooks (:fix)
  ///

  (defret ienv->uchar-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable posp))))

  (defrulel lemma
    (>= (expt 2 (ienv->char-bits ienv)) 256)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 8) (n (ienv->char-bits ienv)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret ienv->uchar-max-lower-bound
    (>= max 255)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->schar-max ((ienv ienvp))
  :returns (max posp :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of @('SCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the discussion in @(tsee schar-format),
     this is always @($2^{\\mathtt{CHAR\\_BIT}-1} - 1$).
     "))
  (1- (expt 2 (1- (ienv->char-bits ienv))))
  :hooks (:fix)
  ///

  (defret ienv->schar-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable posp))))

  (defrulel lemma
    (>= (expt 2 (1- (ienv->char-bits ienv))) 128)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 7) (n (1- (ienv->char-bits ienv))))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret ienv->schar-max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->schar-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('SCHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the discussion in @(tsee schar-format),
     this is either @($- 2^{\\mathtt{CHAR\\_BIT}-1}$)
     (if the signed format is two's complement
     and the pattern with sign bit 1 and all value bits 0
     is not a trap representation)
     or @($- 2^{\\mathtt{CHAR\\_BIT}-1} + 1$)
     (if the signed format is ones' complement or sign-and-magnitude,
     or it is two's complement
     but the pattern with sign bit 1 and all value bits 0
     is a trap representation)."))
  (if (and (equal (signed-format-kind
                   (schar-format->signed (ienv->schar-format ienv)))
                  :twos-complement)
           (not (schar-format->trap (ienv->schar-format ienv))))
      (- (expt 2 (1- (ienv->char-bits ienv))))
    (- (1- (expt 2 (1- (ienv->char-bits ienv))))))
  :hooks (:fix)
  ///

  (defret ienv->schar-min-type-prescription
    (and (integerp min)
         (< min 0))
    :rule-classes :type-prescription)

  (defrulel lemma
    (>= (expt 2 (1- (ienv->char-bits ienv))) 128)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 7) (n (1- (ienv->char-bits ienv))))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret ienv->schar-min-upper-bound
    (<= min (if (and (equal (signed-format-kind
                             (schar-format->signed (ienv->schar-format ienv)))
                            :twos-complement)
                     (not (schar-format->trap (ienv->schar-format ienv))))
                -128
              -127))
    :rule-classes ((:linear :trigger-terms ((ienv->schar-min ienv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-max ((ienv ienvp))
  :returns (max integerp)
  :short "The ACL2 integer value of @('CHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [C17:5.2.4.2.1/2],
     this is either 0 or the same as @('SCHAR_MIN')."))
  (if (char-format->signedp (ienv->char-format ienv))
      (ienv->schar-max ienv)
    (ienv->uchar-max ienv))
  :hooks (:fix)
  ///

  (defret ienv->char-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable posp))))

  (defret ienv->char-max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('CHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [C17:5.2.4.2.1/2],
     this is either 0 or the same as @('SCHAR_MIN')."))
  (if (char-format->signedp (ienv->char-format ienv))
      (ienv->schar-min ienv)
    0)
  :hooks (:fix)
  ///

  (defret ienv->char-min-type-prescription
    (and (integerp min)
         (<= min 0))
    :rule-classes :type-prescription)

  (defret ienv->char-min-upper-bound
    (<= min (if (char-format->signedp (ienv->char-format ienv))
                (if (and (equal (signed-format-kind
                                 (schar-format->signed (ienv->schar-format ienv)))
                                :twos-complement)
                         (not (schar-format->trap (ienv->schar-format ienv))))
                    -128
                  -127)
              0))
    :rule-classes ((:linear :trigger-terms ((ienv->char-min ienv))))))
