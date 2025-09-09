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

(include-book "../../insertion-sort")
(include-book "../../insertion-sort-of-integers-from-to")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

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
     This is required to be at least 8 [C17:5.2.4.2.1/1].")
   (xdoc::p
    "We use the name @('size') for the number of bits,
     i.e. the size (in bits) of @('unsigned char') objects."))
  ((size nat :reqfix (if (>= size 8) size 8)))
  :require (>= size 8)
  :pred uchar-formatp
  :prepwork ((local (in-theory (enable nfix))))
  ///

  (defret uchar-format->size-type-prescription
    (and (posp size)
         (> size 1))
    :fn uchar-format->size
    :rule-classes :type-prescription)

  (defret uchar-format->size-lower-bound
    (>= size 8)
    :fn uchar-format->size
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-format->max ((format uchar-formatp))
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
  (1- (expt 2 (uchar-format->size format)))
  :hooks (:fix)
  ///

  (defret uchar-format->-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable posp))))

  (defrulel lemma
    (>= (expt 2 (uchar-format->size format)) 256)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 8) (n (uchar-format->size format)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret uchar-format->max-lower-bound
    (>= max 255)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-format-8 ()
  :returns (format uchar-formatp)
  :short "The @('unsigned char') format defined by 8 bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and most common format for @('unsigned char')."))
  (make-uchar-format :size 8)

  ///

  (defruled uchar-format->max-of-uchar-format-8
    (equal (uchar-format->max (uchar-format-8))
           255)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schar-format->max ((schar-format schar-formatp)
                           (uchar-format uchar-formatp))
  :returns (max posp :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of @('SCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the discussion in @(tsee schar-format),
     this is always @($2^{\\mathtt{CHAR\\_BIT}-1} - 1$).")
   (xdoc::p
    "This depends on @('CHAR_BIT'),
     so this function also takes the @('unsigned char') format as input.
     In fact, this function only depends on @('CHAR_BIT'),
     but we include the @('signed char') format as input for uniformity."))
  (declare (ignore schar-format))
  (1- (expt 2 (1- (uchar-format->size uchar-format))))
  :hooks (:fix)
  ///

  (defret schar-format->max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable posp))))

  (defrulel lemma
    (>= (expt 2 (1- (uchar-format->size uchar-format))) 128)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 7) (n (1- (uchar-format->size uchar-format))))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret schar-format->max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schar-format->min ((schar-format schar-formatp)
                           (uchar-format uchar-formatp))
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
     is a trap representation).")
   (xdoc::p
    "Like @(tsee schar-format->max),
     this function also depends on the @('unsigned char') format.
     Unlike @(tsee schar-format->max),
     this function also depends on the @('signed char') format."))
  (if (and (equal (signed-format-kind
                   (schar-format->signed schar-format))
                  :twos-complement)
           (not (schar-format->trap schar-format)))
      (- (expt 2 (1- (uchar-format->size uchar-format))))
    (- (1- (expt 2 (1- (uchar-format->size uchar-format))))))
  :hooks (:fix)
  ///

  (defret schar-format->min-type-prescription
    (and (integerp min)
         (< min 0))
    :rule-classes :type-prescription)

  (defrulel lemma
    (>= (expt 2 (1- (uchar-format->size uchar-format))) 128)
    :rule-classes :linear
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                    (x 2) (m 7) (n (1- (uchar-format->size uchar-format))))
    :disable acl2::expt-is-weakly-increasing-for-base->-1)

  (defret schar-format->min-upper-bound
    (<= min -127)
    :rule-classes
    ((:linear
      :trigger-terms ((schar-format->min schar-format uchar-format))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schar-format-8tcnt ()
  :returns (format schar-formatp)
  :short "The @('signed char') format defined by
          8 bits, two's complement, and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and most common format for @('signed char')."))
  (make-schar-format :signed (signed-format-twos-complement)
                     :trap nil)

  ///

  (defruled schar-format->max-of-schar-format-8tcnt
    (equal (schar-format->max (schar-format-8tcnt) (uchar-format-8))
           127))

  (defruled schar-format->min-of-schar-format-8tcnt
    (equal (schar-format->min (schar-format-8tcnt) (uchar-format-8))
           -128)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-format->max ((char-format char-formatp)
                          (uchar-format uchar-formatp)
                          (schar-format schar-formatp))
  :returns (max posp)
  :short "The ACL2 integer value of @('CHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [C17:5.2.4.2.1/2],
     this is the same as either @('UCHAR_MAX') or @('SCHAR_MAX')."))
  (if (char-format->signedp char-format)
      (schar-format->max schar-format uchar-format)
    (uchar-format->max uchar-format))
  :hooks (:fix)
  ///

  (defret char-format->max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defret char-format->max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-format->min ((char-format char-formatp)
                          (uchar-format uchar-formatp)
                          (schar-format schar-formatp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('CHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [C17:5.2.4.2.1/2],
     this is either 0 or the same as @('SCHAR_MIN')."))
  (if (char-format->signedp char-format)
      (schar-format->min schar-format uchar-format)
    0)
  :hooks (:fix)
  ///

  (defret char-format->min-type-prescription
    (and (integerp min)
         (<= min 0))
    :rule-classes :type-prescription)

  (defret char-format->min-upper-bound
    (<= min 0)
    :rule-classes
    ((:linear
      :trigger-terms
      ((char-format->min char-format uchar-format schar-format))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-format-8u ()
  :returns (format char-formatp)
  :short "The @('char') format defined by 8 bits and unsignedness."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest format of @('char').
     It is not clear whether it is the most common or not."))
  (make-char-format :signedp nil)

  ///

  (defruled char-format->max-of-char-format-8u
    (equal (char-format->max (char-format-8u)
                             (uchar-format-8)
                             (schar-format-8tcnt))
           255))

  (defruled char-format->min-of-char-format-8u
    (equal (char-format->min (char-format-8u)
                             (uchar-format-8)
                             (schar-format-8tcnt))
           0)))

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

(define sinteger-bit-roles-sign-count ((roles sinteger-bit-role-listp))
  :returns (count natp)
  :short "Number of sign bit roles in a list of roles of signed integer bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "We count the number of sign bit roles.
     Note that the sign bit roles in a list are all the same."))
  (cond ((endp roles) 0)
        ((sinteger-bit-role-case (car roles) :sign)
         (1+ (sinteger-bit-roles-sign-count (cdr roles))))
        (t (sinteger-bit-roles-sign-count (cdr roles))))
  :hooks (:fix)

  ///

  (defruled sinteger-bit-roles-sign-count-of-append
    (equal (sinteger-bit-roles-sign-count (append roles1 roles2))
           (+ (sinteger-bit-roles-sign-count roles1)
              (sinteger-bit-roles-sign-count roles2)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-bit-roles-exponents ((roles uinteger-bit-role-listp))
  :returns (exponents nat-listp)
  :short "Exponents of a list of roles of unsigned integer bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect the list of exponents of the value bit roles,
     in the same order as they occur in the list of bit roles,
     skipping over the padding bit roles."))
  (b* (((when (endp roles)) nil)
       (role (car roles))
       ((unless (uinteger-bit-role-case role :value))
        (uinteger-bit-roles-exponents (cdr roles))))
    (cons (uinteger-bit-role-value->exp role)
          (uinteger-bit-roles-exponents (cdr roles))))
  :hooks (:fix)

  ///

  (defruled uinteger-bit-roles-exponents-of-append
    (equal (uinteger-bit-roles-exponents (append roles1 roles2))
           (append (uinteger-bit-roles-exponents roles1)
                   (uinteger-bit-roles-exponents roles2)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-bit-roles-exponents ((roles sinteger-bit-role-listp))
  :returns (exponents nat-listp)
  :short "Exponents of a list of roles of signed integer bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect the list of exponents of the value bit roles,
     in the same order as they occur in the list of bit roles,
     skipping over the padding and sign bit roles."))
  (b* (((when (endp roles)) nil)
       (role (car roles))
       ((unless (sinteger-bit-role-case role :value))
        (sinteger-bit-roles-exponents (cdr roles))))
    (cons (sinteger-bit-role-value->exp role)
          (sinteger-bit-roles-exponents (cdr roles))))
  :hooks (:fix)

  ///

  (defruled sinteger-bit-roles-exponents-of-append
    (equal (sinteger-bit-roles-exponents (append roles1 roles2))
           (append (sinteger-bit-roles-exponents roles1)
                   (sinteger-bit-roles-exponents roles2)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-bit-roles-value-count ((roles uinteger-bit-role-listp))
  :returns (n natp)
  :short "Number of value bit roles in
          a list of roles of unsigned integer bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the list of bit roles is well-formed
     (see @(tsee uinteger-bit-roles-wfp)),
     this is the number @('N') of value bits [C17:6.2.6.2/1],
     whose associated exponents go from @('0') to @('N-1')."))
  (cond ((endp roles) 0)
        ((uinteger-bit-role-case (car roles) :value)
         (1+ (uinteger-bit-roles-value-count (cdr roles))))
        (t (uinteger-bit-roles-value-count (cdr roles))))
  :hooks (:fix)

  ///

  (defruled uinteger-bit-roles-value-count-alt-def
    (equal (uinteger-bit-roles-value-count roles)
           (len (uinteger-bit-roles-exponents roles)))
    :induct t
    :enable (uinteger-bit-roles-exponents len))

  (defruled uinteger-bit-roles-value-count-of-append
    (equal (uinteger-bit-roles-value-count (append roles1 roles2))
           (+ (uinteger-bit-roles-value-count roles1)
              (uinteger-bit-roles-value-count roles2)))
    :induct t)

  (defruled uinteger-bit-roles-value-count-upper-bound
    (<= (uinteger-bit-roles-value-count roles)
        (len roles))
    :rule-classes :linear
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-bit-roles-value-count ((roles sinteger-bit-role-listp))
  :returns (m natp)
  :short "Number of value bit roles in
          a list of roles of signed integer bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the list of bit roles is well-formed
     (see @(tsee sinteger-bit-roles-wfp)),
     this is the number @('M') of value bits [C17:6.2.6.2/2],
     whose associated exponents go from @('0') to @('M-1')."))
  (cond ((endp roles) 0)
        ((sinteger-bit-role-case (car roles) :value)
         (1+ (sinteger-bit-roles-value-count (cdr roles))))
        (t (sinteger-bit-roles-value-count (cdr roles))))
  :hooks (:fix)

  ///

  (defruled sinteger-bit-roles-value-count-alt-def
    (equal (sinteger-bit-roles-value-count roles)
           (len (sinteger-bit-roles-exponents roles)))
    :induct t
    :enable (sinteger-bit-roles-exponents len))

  (defruled sinteger-bit-roles-value-count-of-append
    (equal (sinteger-bit-roles-value-count (append roles1 roles2))
           (+ (sinteger-bit-roles-value-count roles1)
              (sinteger-bit-roles-value-count roles2)))
    :induct t)

  (defruled sinteger-bit-roles-value/sign-count-upper-bound
    (<= (+ (sinteger-bit-roles-value-count roles)
           (sinteger-bit-roles-sign-count roles))
        (len roles))
    :rule-classes :linear
    :induct t
    :enable sinteger-bit-roles-sign-count)

  (defruled sinteger-bit-roles-value-count-upper-bound
    (<= (sinteger-bit-roles-value-count roles)
        (- (len roles)
           (sinteger-bit-roles-sign-count roles)))
    :enable sinteger-bit-roles-value/sign-count-upper-bound))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-bit-roles-wfp ((roles uinteger-bit-role-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of roles of unsigned integer bits is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [C17:6.2.6.2/1],
     there must be exactly one value bit for each exponent
     in a range from 0 to @('N-1') for some @('N').
     We express that by saying that,
     after collecting the exponents and sorting them,
     we must have the list @('(0 1 ... N-1)'),
     where @('N') is the number of collected exponents.
     Note that this prohibits duplicates.
     We also require @('N') to be non-zero,
     although this is not explicated in [C17]."))
  (b* ((exponents (uinteger-bit-roles-exponents roles))
       (n (len exponents))
       ((when (= n 0)) nil)
       (sorted-exponents (insertion-sort exponents))
       ((unless (equal sorted-exponents
                       (integers-from-to 0 (1- n))))
        nil))
    t)
  :hooks (:fix)

  ///

  (defruled posp-of-uinteger-bit-roles-value-count-when-wfp
    (implies (uinteger-bit-roles-wfp roles)
             (posp (uinteger-bit-roles-value-count roles)))
    :rule-classes (:rewrite :type-prescription)
    :enable (uinteger-bit-roles-wfp
             uinteger-bit-roles-value-count-alt-def))

  (defruled len-gt-0-when-uinteger-bit-roles-wfp
    (implies (uinteger-bit-roles-wfp roles)
             (> (len roles) 0))
    :enable (uinteger-bit-roles-wfp
             uinteger-bit-roles-value-count-alt-def
             uinteger-bit-roles-value-count-upper-bound)
    :disable (acl2::|(< 0 (len x))|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-bit-roles-wfp ((roles sinteger-bit-role-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of roles of signed integer bits is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [C17:6.2.6.2/2],
     there must be exactly one value bit for each exponent
     in a range from 0 to @('M-1') for some @('M').
     We express that by saying that,
     after collecting the exponents and sorting them,
     we must have the list @('(0 1 ... M-1)'),
     where @('M') is the number of collected exponents.
     Note that this prohibits duplicates.
     We also require @('M') to be non-zero,
     although this is not explicated in [C17].")
   (xdoc::p
    "[C17:6.2.6.2/2] also says that there must be exactly one sign bit,
     i.e. the number of sign bits must be 1."))
  (b* ((exponents (sinteger-bit-roles-exponents roles))
       (m (len exponents))
       ((when (= m 0)) nil)
       (sorted-exponents (insertion-sort exponents))
       ((unless (equal sorted-exponents
                       (integers-from-to 0 (1- m))))
        nil)
       ((unless (= (sinteger-bit-roles-sign-count roles) 1)) nil))
    t)
  :hooks (:fix)

  ///

  (defruled posp-of-sinteger-bit-roles-value-count-when-wfp
    (implies (sinteger-bit-roles-wfp roles)
             (posp (sinteger-bit-roles-value-count roles)))
    :rule-classes (:rewrite :type-prescription)
    :enable (sinteger-bit-roles-wfp
             sinteger-bit-roles-value-count-alt-def))

  (defruled len-gt-1-when-sinteger-bit-roles-wfp
    (implies (sinteger-bit-roles-wfp roles)
             (> (len roles) 1))
    :enable (sinteger-bit-roles-wfp
             sinteger-bit-roles-value-count-alt-def
             sinteger-bit-roles-value/sign-count-upper-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-sinteger-bit-roles-wfp ((uroles uinteger-bit-role-listp)
                                         (sroles sinteger-bit-role-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of roles of unsigned integer bits
          and a list of roles of signed integer bits
          are mutually consistent."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.2.6.2/2] says each signed integer value bit
     must be the same as the corresponding unsigned integer value bit;
     but the unsigned integer type may have more value bits.
     We check this by going through the two lists of bits,
     and making sure that, every time we encounter a signed value bit,
     the corresponding unsigned value bit is for the same exponent.")
   (xdoc::p
    "[C17:6.2.5/6] says that corresponding signed and unsigned integer types
     take the same amount of storage.
     In our model, it means that they must have the same number of bits.
     We check this requirement in this recursive predicate,
     by ensuring that the two lists end at the same time.")
   (xdoc::p
    "We show that this predicate guarantees
     the inequality @('M <= N') mentioned in [C17:6.2.6.2/2]."))
  (b* (((when (endp uroles)) (endp sroles))
       ((when (endp sroles)) nil)
       (srole (car sroles))
       ((unless (sinteger-bit-role-case srole :value))
        (uinteger-sinteger-bit-roles-wfp (cdr uroles) (cdr sroles)))
       (urole (car uroles))
       ((unless (and (uinteger-bit-role-case urole :value)
                     (equal (uinteger-bit-role-value->exp urole)
                            (sinteger-bit-role-value->exp srole))))
        nil))
    (uinteger-sinteger-bit-roles-wfp (cdr uroles) (cdr sroles)))
  :hooks (:fix)

  ///

  (defruled same-len-when-uinteger-sinteger-bit-roles-wfp
    (implies (uinteger-sinteger-bit-roles-wfp uroles sroles)
             (equal (len uroles)
                    (len sroles)))
    :rule-classes (:rewrite :forward-chaining)
    :induct t
    :enable len)

  (defruled sinteger-value-bits-leq-uinteger-value-bits
    (implies (uinteger-sinteger-bit-roles-wfp uroles sroles)
             (<= (sinteger-bit-roles-value-count sroles)
                 (uinteger-bit-roles-value-count uroles)))
    :induct t
    :enable (sinteger-bit-roles-value-count
             uinteger-bit-roles-value-count))

  (defruled uinteger-sinteger-bit-roles-wfp-of-append
    (implies (equal (len uroles1) (len sroles1))
             (equal (uinteger-sinteger-bit-roles-wfp (append uroles1 uroles2)
                                                     (append sroles1 sroles2))
                    (and (uinteger-sinteger-bit-roles-wfp uroles1 sroles1)
                         (uinteger-sinteger-bit-roles-wfp uroles2 sroles2))))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-bit-roles-inc-n ((n natp))
  :returns (roles uinteger-bit-role-listp)
  :short "List of @('n') unsigned integer value bit roles,
          starting with exponent 0, in increasing exponent order."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of bit roles is well-formed, if @('n') is not 0."))
  (b* (((when (zp n)) nil)
       (role (uinteger-bit-role-value (1- n)))
       (roles (uinteger-bit-roles-inc-n (1- n))))
    (append roles (list role)))
  :prepwork ((local (in-theory (enable nfix))))
  :hooks (:fix)

  ///

  (defret len-of-uinteger-bit-roles-inc-n
    (equal (len roles)
           (nfix n))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defruled uinteger-bit-roles-exponents-of-uinteger-bit-roles-inc-n
    (equal (uinteger-bit-roles-exponents
            (uinteger-bit-roles-inc-n n))
           (integers-from-to 0 (1- (nfix n))))
    :induct t
    :enable (uinteger-bit-roles-exponents
             uinteger-bit-roles-exponents-of-append
             acl2::integers-from-to-separate-max
             ifix
             nfix))

  (defruled uinteger-bit-roles-value-count-of-uinteger-bit-roles-inc-n
    (equal (uinteger-bit-roles-value-count
            (uinteger-bit-roles-inc-n n))
           (nfix n))
    :enable (uinteger-bit-roles-value-count-alt-def
             uinteger-bit-roles-exponents-of-uinteger-bit-roles-inc-n
             acl2::len-of-integers-from-to
             ifix)
    :disable uinteger-bit-roles-inc-n)

  (defruled uinteger-bit-roles-wfp-of-uinteger-bit-roles-inc-n
    (implies (not (zp n))
             (uinteger-bit-roles-wfp
              (uinteger-bit-roles-inc-n n)))
    :disable uinteger-bit-roles-inc-n
    :enable (uinteger-bit-roles-wfp
             uinteger-bit-roles-exponents-of-uinteger-bit-roles-inc-n
             atom
             acl2::len-of-integers-from-to
             ifix
             insertion-sort-of-integers-from-to)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-bit-roles-inc-n ((n natp))
  :returns (roles sinteger-bit-role-listp)
  :short "List of @('n') signed integer value bit roles,
          starting with exponent 0, in increasing exponent order."
  (b* (((when (zp n)) nil)
       (role (sinteger-bit-role-value (1- n)))
       (roles (sinteger-bit-roles-inc-n (1- n))))
    (append roles (list role)))
  :prepwork ((local (in-theory (enable nfix))))
  :hooks (:fix)

  ///

  (defret len-of-sinteger-bit-roles-inc-n
    (equal (len roles)
           (nfix n))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defruled sinteger-bit-roles-exponents-of-sinteger-bit-roles-inc-n
    (equal (sinteger-bit-roles-exponents
            (sinteger-bit-roles-inc-n n))
           (integers-from-to 0 (1- (nfix n))))
    :induct t
    :enable (sinteger-bit-roles-exponents
             sinteger-bit-roles-exponents-of-append
             acl2::integers-from-to-separate-max
             ifix
             nfix))

  (defruled sinteger-bit-roles-value-count-of-sinteger-bit-roles-inc-n
    (equal (sinteger-bit-roles-value-count
            (sinteger-bit-roles-inc-n n))
           (nfix n))
    :disable sinteger-bit-roles-inc-n
    :enable (sinteger-bit-roles-value-count-alt-def
             sinteger-bit-roles-exponents-of-sinteger-bit-roles-inc-n
             acl2::len-of-integers-from-to
             ifix))

  (defruled sinteger-bit-roles-sign-count-of-sinteger-bit-roles-inc-n
    (equal (sinteger-bit-roles-sign-count (sinteger-bit-roles-inc-n n))
           0)
    :induct t
    :enable (sinteger-bit-roles-sign-count-of-append
             sinteger-bit-roles-sign-count)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-bit-roles-inc-n-and-sign ((n natp))
  :returns (roles sinteger-bit-role-listp)
  :short "List of @('n') signed integer value bit roles,
          starting with exponent 0, in increasing exponent order,
          and with a sign bit added at the end."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of bit roles is well-formed, if @('n') is not 0."))
  (append (sinteger-bit-roles-inc-n n)
          (list (sinteger-bit-role-sign)))
  :hooks (:fix)

  ///

  (defruled sinteger-bit-roles-wfp-of-sinteger-bit-roles-inc-n-and-sign
    (implies (not (zp n))
             (sinteger-bit-roles-wfp
              (sinteger-bit-roles-inc-n-and-sign n)))
    :enable (sinteger-bit-roles-wfp
             sinteger-bit-roles-exponents-of-append
             sinteger-bit-roles-exponents-of-sinteger-bit-roles-inc-n
             atom
             ifix
             sinteger-bit-roles-sign-count-of-append
             sinteger-bit-roles-sign-count-of-sinteger-bit-roles-inc-n
             insertion-sort-of-integers-from-to
             acl2::len-of-integers-from-to))

  (defruled sinteger-bit-roles-exponents-of-sinteger-bit-roles-inc-n-and-sign
    (equal (sinteger-bit-roles-exponents
            (sinteger-bit-roles-inc-n-and-sign n))
           (integers-from-to 0 (1- (nfix n))))
    :enable (sinteger-bit-roles-exponents-of-append
             sinteger-bit-roles-exponents-of-sinteger-bit-roles-inc-n))

  (defruled sinteger-bit-roles-value-count-of-sinteger-bit-roles-inc-n-and-sign
    (equal (sinteger-bit-roles-value-count
            (sinteger-bit-roles-inc-n-and-sign n))
           (nfix n))
    :enable (sinteger-bit-roles-value-count-of-append
             sinteger-bit-roles-value-count-of-sinteger-bit-roles-inc-n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled uinteger-sinteger-bit-roles-wfp-of-inc-n-and-sign
  :short "Mutual well-formedness of the lists of bit roles
          from @(tsee uinteger-bit-roles-inc-n)
          and @(tsee sinteger-bit-roles-inc-n-and-sign)."
  (implies (and (natp n)
                (>= n 2))
           (uinteger-sinteger-bit-roles-wfp
            (uinteger-bit-roles-inc-n n)
            (sinteger-bit-roles-inc-n-and-sign (1- n))))
  :induct t
  :enable (uinteger-sinteger-bit-roles-wfp
           uinteger-bit-roles-inc-n
           sinteger-bit-roles-inc-n-and-sign
           sinteger-bit-roles-inc-n
           uinteger-sinteger-bit-roles-wfp-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uinteger-format
  :short "Fixtype of formats of unsigned integer objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for unsigned integer objects
     other than those of type @('unsigned char'),
     which are covered by @(tsee uchar-format).
     See [C17:6.2.6.2./1].")
   (xdoc::p
    "The format definition includes a list of bit roles,
     which should be thought as the juxtaposition of
     the bytes that form the unsigned integer object,
     in little endian order, i.e. from lower to higher address.
     The length of the list of bit roles
     must be a mulitple of @('CHAR_BIT'),
     which we capture in @(tsee uchar-format):
     we express this constraint elsewhere,
     because we do not have that value available here.
     The list of bit roles must be well-formed.")
   (xdoc::p
    "We also include a placeholder component meant to define
     which bit values are trap representations [C17:6.2.6.2/5].
     We plan to flesh this out in the future."))
  ((bits uinteger-bit-role-listp
         :reqfix (if (uinteger-bit-roles-wfp bits)
                     bits
                   (list (uinteger-bit-role-value 0))))
   traps)
  :require (uinteger-bit-roles-wfp bits)
  :pred uinteger-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod sinteger-format
  :short "Fixtype of formats of signed integer objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for signed integer objects
     other than those of type @('signed char'),
     which are covered by @(tsee schar-format).
     See [C17:6.2.6.2./2].")
   (xdoc::p
    "The format definition includes a list of bit roles,
     which should be thought as the juxtaposition of
     the bytes that form the unsigned integer object,
     in little endian order, i.e. from lower to higher address.
     The length of the list of bit roles
     must be a mulitple of @('CHAR_BIT'),
     which we capture in @(tsee uchar-format):
     we express this constraint elsewhere,
     because we do not have that value available here.
     The list of bit roles must be well-formed.")
   (xdoc::p
    "The format description also identifies one of the three signed formats.
     It is not clear from [C17] whether all the signed integer type,
     within an implementation, use that same signed format,
     but out model allows them to differ.")
   (xdoc::p
    "We also include a placeholder component meant to define
     which bit values are trap representations [C17:6.2.6.2/5].
     We plan to flesh this out in the future."))
  ((bits sinteger-bit-role-listp
         :reqfix (if (sinteger-bit-roles-wfp bits)
                     bits
                   (list (sinteger-bit-role-sign)
                         (sinteger-bit-role-value 0))))
   (signed signed-format)
   traps)
  :require (sinteger-bit-roles-wfp bits)
  :pred sinteger-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-format->max ((format uinteger-formatp))
  :returns (max posp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of
          the maximum value representable in an unsigned integer format."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is determined by the number @('N') of value bits:
     the maximum value is @('2^N - 1').")
   (xdoc::p
    "Since @('N <= T'), where @('T') is the total number of bits,
     the maximum value cannot be above @('2^T - 1')."))
  (1- (expt 2 (uinteger-bit-roles-value-count
               (uinteger-format->bits format))))
  :hooks (:fix)

  ///

  (defret uinteger-format->max-upper-bound
    (<= max
        (1- (expt 2 (len (uinteger-format->bits format)))))
    :rule-classes :linear
    :hints
    (("Goal" :in-theory (enable uinteger-bit-roles-value-count-upper-bound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-format->max ((format sinteger-formatp))
  :returns (max posp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of
          the maximum value representable in a signed integer format."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is determined by the number @('M') of value bits:
     the maximum value is @('2^M - 1').")
   (xdoc::p
    "Since @('M <= T - 1'), where @('T') is the total number of bits,
     and where the 1 accounts for the sign bit,
     the maximum value cannot be above @('2^(T-1) - 1')."))
  (1- (expt 2 (sinteger-bit-roles-value-count
               (sinteger-format->bits format))))
  :hooks (:fix)

  ///

  (defret sinteger-format->max-upper-bound
    (<= max
        (1- (expt 2 (1- (len (sinteger-format->bits format))))))
    :rule-classes :linear
    :hints
    (("Goal"
      :in-theory (e/d (sinteger-bit-roles-wfp)
                      (sinteger-format-requirements
                       acl2::expt-is-weakly-increasing-for-base->-1
                       acl2::|(* (expt x m) (/ (expt x n)))|
                       acl2::|(* a (/ a))|
                       acl2::bubble-down-*-match-1
                       acl2::bubble-down-*-match-2
                       acl2::simplify-products-gather-exponents-<
                       acl2::expt-is-weakly-increasing-for-base->-1
                       acl2::expt-is-increasing-for-base->-1))
      :use ((:instance sinteger-format-requirements (x format))
            (:instance acl2::expt-is-weakly-increasing-for-base->-1
                       (x 2)
                       (m (sinteger-bit-roles-value-count
                           (sinteger-format->bits format)))
                       (n (1- (len (sinteger-format->bits format)))))
            (:instance sinteger-bit-roles-value-count-upper-bound
                       (roles (sinteger-format->bits format))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-format->min ((format sinteger-formatp))
  :returns (min integerp)
  :short "The ACL2 integer value of
          the minimum value representable in a signed integer format."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is determined by the number @('M') of value bits,
     the signed format, and possibly the trap representations
     [C17:6.2.6.2/2].
     If the signed format is either sign and magnitude or ones' complement,
     the minimum value is the negation of the maximum value,
     i.e. @('- (2^M - 1)').
     If the signed format is two's complement,
     there are two possibilities:
     if the representation with sign bit 1 and all value bits 0
     is a trap representation,
     the minimum value is @('- (2^M - 1)');
     otherwise, it is @('- 2^M').
     As explained in @(tsee sinteger-format),
     currently we do not have a detailed model of trap representations;
     as a placeholder, for now we regard that representation to be a trap one
     iff the @('traps') component of @(tsee sinteger-format) is not @('nil').")
   (xdoc::p
    "Since @('M <= T - 1'), where @('T') is the total number of bits,
     and where the 1 accounts for the sign bit,
     the minimum value cannot be below @('- 2^(T-1)')."))
  (if (and (equal (signed-format-kind (sinteger-format->signed format))
                  :twos-complement)
           (not (sinteger-format->traps format)))
      (- (expt 2 (sinteger-bit-roles-value-count
                  (sinteger-format->bits format))))
    (- (1- (expt 2 (sinteger-bit-roles-value-count
                    (sinteger-format->bits format))))))
  :hooks (:fix)

  ///

  (defret sinteger-format->min-type-prescription
    (and (integerp min)
         (< min 0))
    :rule-classes :type-prescription)

  (defret sinteger-format->min-lower-bound
    (>= min
        (- (expt 2 (1- (len (sinteger-format->bits format))))))
    :rule-classes :linear
    :hints
    (("Goal"
      :in-theory (e/d (sinteger-bit-roles-wfp)
                      (sinteger-format-requirements
                       acl2::expt-is-weakly-increasing-for-base->-1
                       acl2::|(* (expt x m) (/ (expt x n)))|
                       acl2::|(* a (/ a))|
                       acl2::bubble-down-*-match-1
                       acl2::bubble-down-*-match-2
                       acl2::simplify-products-gather-exponents-<
                       acl2::expt-is-weakly-increasing-for-base->-1
                       acl2::expt-is-increasing-for-base->-1))
      :use ((:instance sinteger-format-requirements (x format))
            (:instance acl2::expt-is-weakly-increasing-for-base->-1
                       (x 2)
                       (m (sinteger-bit-roles-value-count
                           (sinteger-format->bits format)))
                       (n (1- (len (sinteger-format->bits format)))))
            (:instance sinteger-bit-roles-value-count-upper-bound
                       (roles (sinteger-format->bits format))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uinteger-format-inc-npnt ((n posp))
  :returns (format uinteger-formatp)
  :short "The unsigned integer format defined by
          @('n') increasing value bits,
          no padding bits,
          and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is parameterized over @('n'), which must be positiive."))
  (make-uinteger-format
   :bits (uinteger-bit-roles-inc-n (pos-fix n))
   :traps nil)
  :hooks (:fix)

  ///

  (defruled uinteger-format->max-of-uinteger-format-inc-npnt
    (equal (uinteger-format->max (uinteger-format-inc-npnt n))
           (1- (expt 2 (pos-fix n))))
    :enable (uinteger-format->max
             pos-fix
             uinteger-bit-roles-value-count-of-uinteger-bit-roles-inc-n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sinteger-format-inc-sign-tcnpnt ((n posp))
  :returns (format sinteger-formatp)
  :short "The signed integer format defined by
          @('n') increasing value bits,
          a sign bit at the end,
          two's complement signed format,
          no padding bits,
          and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is parameterized over @('n'), which must be positiive."))
  (make-sinteger-format
   :bits (sinteger-bit-roles-inc-n-and-sign (pos-fix n))
   :signed (signed-format-twos-complement)
   :traps nil)
  :hooks (:fix)

  ///

  (defruled sinteger-format->max-of-sinteger-format-inc-sign-tcnpnt
    (equal (sinteger-format->max (sinteger-format-inc-sign-tcnpnt n))
           (1- (expt 2 (pos-fix n))))
    :enable
    (sinteger-format->max
     sinteger-bit-roles-value-count-of-sinteger-bit-roles-inc-n-and-sign))

  (defruled sinteger-format->min-of-sinteger-format-inc-sign-tcnpnt
    (equal (sinteger-format->min (sinteger-format-inc-sign-tcnpnt n))
           (- (expt 2 (pos-fix n))))
    :enable
    (sinteger-format->min
     sinteger-bit-roles-value-count-of-sinteger-bit-roles-inc-n-and-sign)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uinteger+sinteger-format
  :short "Fixtype of pairs consisting of
          a format of unsigned integer objects
          and a format of signed integer objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "This just puts together an unsigned format with a signed format.
     It is a preliminary definition used for @(tsee integer-format)."))
  ((unsigned uinteger-format)
   (signed sinteger-format))
  :pred uinteger+sinteger-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod integer-format
  :short "Fixtype of formats of (signed and unsigned) integer objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each signed integer type has a corresponding unsigned integer type
     [C17:6.2.5/6].
     There are constraints between the representations of
     two corresponding signed and unsigned integer types
     [C17:6.2.6.2/2].
     Thus, we introduce a notion for the format of
     corresponding unsigned and signed integer types.
     This is for @('signed short') and @('unsigned short'),
     or for @('signed int') and @('unsigned int'),
     etc.
     This consists of a an unsigned and a signed integer format,
     constrained to be well-formed relative to each other.")
   (xdoc::p
    "The reason for introducing and using
     the ``intermediate'' fixtype @(tsee uinteger+sinteger-format),
     as opposed to directly define this @('integer-format') fixtype
     to consists of the two components of that intermediate type
     is the following.
     We want this @('integer-format') fixtype to require (in @(':require'))
     the consistency between the unsigned and signed integer formats
     (i.e. @(tsee uinteger-sinteger-bit-roles-wfp)).
     But if we have two separate components,
     we need separate fixers (in @(':reqfix') for the two components,
     which we plan to define later as they may take a bit of work.
     Once we have the proofs,
     we will eliminate the intermediate fixtype @(tsee uinteger+sinteger-format)
     and have two components and two fixers in this fixtype here."))
  ((pair uinteger+sinteger-format
         :reqfix (if (uinteger-sinteger-bit-roles-wfp
                      (uinteger-format->bits
                       (uinteger+sinteger-format->unsigned pair))
                      (sinteger-format->bits
                       (uinteger+sinteger-format->signed pair)))
                     pair
                   (make-uinteger+sinteger-format
                    :unsigned (make-uinteger-format
                               :bits (list (uinteger-bit-role-value 0)
                                           (uinteger-bit-role-value 1))
                               :traps nil)
                    :signed (make-sinteger-format
                             :bits (list (sinteger-bit-role-value 0)
                                         (sinteger-bit-role-sign))
                             :signed (signed-format-twos-complement)
                             :traps nil)))))
  :require (uinteger-sinteger-bit-roles-wfp
            (uinteger-format->bits
             (uinteger+sinteger-format->unsigned pair))
            (sinteger-format->bits
             (uinteger+sinteger-format->signed pair)))
  :pred integer-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format->bit-size ((format integer-formatp))
  :returns (size posp :hints (("Goal" :in-theory (enable posp))))
  :short "Number of bits of an integer format."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the total number of bits of the unsigned or signed format:
     the two have the same number of bits,
     because of @(tsee uinteger-sinteger-bit-roles-wfp)."))
  (len (uinteger-format->bits
        (uinteger+sinteger-format->unsigned
         (integer-format->pair format))))
  :hooks (:fix)

  ///

  (defruled integer-format->bit-size-alt-def
    (equal (integer-format->bit-size format)
           (len (sinteger-format->bits
                 (uinteger+sinteger-format->signed
                  (integer-format->pair format)))))
    :use (:instance same-len-when-uinteger-sinteger-bit-roles-wfp
                    (sroles (sinteger-format->bits
                             (uinteger+sinteger-format->signed
                              (integer-format->pair format))))
                    (uroles (uinteger-format->bits
                             (uinteger+sinteger-format->unsigned
                              (integer-format->pair format))))))

  (defret integer-format->bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :hyp (integer-formatp format)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (e/d (integer-format->bit-size-alt-def)
                                    (integer-format->bit-size))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format->unsigned-max ((format integer-formatp))
  :returns (max posp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of
          the maximum unsigned value representable in an integer format."
  (uinteger-format->max
   (uinteger+sinteger-format->unsigned
    (integer-format->pair format)))
  :hooks (:fix)

  ///

  (defret integer-format->unsigned-max-upper-bound
    (<= max
        (1- (expt 2 (integer-format->bit-size format))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable integer-format->bit-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format->signed-max ((format integer-formatp))
  :returns (max posp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of
          the maximum signed value representable in an integer format."
  (sinteger-format->max
   (uinteger+sinteger-format->signed
    (integer-format->pair format)))
  :hooks (:fix)

  ///

  (defret integer-format->signed-max-upper-bound
    (<= max
        (1- (expt 2 (1- (integer-format->bit-size format)))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable integer-format->bit-size-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format->signed-min ((format integer-formatp))
  :returns (min integerp)
  :short "The ACL2 integer value of
          the minimum signed value representable in an integer format."
  (sinteger-format->min
   (uinteger+sinteger-format->signed
    (integer-format->pair format)))
  :hooks (:fix)

  ///

  (defret integer-format->signed-min-type-prescription
    (and (integerp min)
         (< min 0))
    :rule-classes :type-prescription)

  (defret integer-format->signed-min-lower-bound
    (>= min
        (- (expt 2 (1- (integer-format->bit-size format)))))
    :hints (("Goal" :in-theory (enable integer-format->bit-size-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format-inc-sign-tcnpnt ((size posp))
  :guard (not (equal size 1))
  :returns (format integer-formatp)
  :short "The unsigned and signed integer format defined by
          a size greater than 1,
          increasing value bits,
          a sign bit at the end (for the signed format),
          two's complement signed format,
          no padding bits,
          and no trap representations."
  (make-integer-format
   :pair (make-uinteger+sinteger-format
          :unsigned (uinteger-format-inc-npnt size)
          :signed (sinteger-format-inc-sign-tcnpnt (1- (pos-fix size)))))
  :verify-guards nil ; done below
  :hooks (:fix)

  ///

  (defruled uinteger-sinteger-bit-roles-wfp-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size)
                  (not (equal size 1)))
             (uinteger-sinteger-bit-roles-wfp
              (uinteger-format->bits
               (uinteger-format-inc-npnt size))
              (sinteger-format->bits
               (sinteger-format-inc-sign-tcnpnt (+ -1 size)))))
    :enable (posp
             uinteger-format-inc-npnt
             sinteger-format-inc-sign-tcnpnt
             uinteger-sinteger-bit-roles-wfp-of-inc-n-and-sign
             sinteger-bit-roles-wfp-of-sinteger-bit-roles-inc-n-and-sign))

  (verify-guards integer-format-inc-sign-tcnpnt
    :hints
    (("Goal"
      :in-theory
      (enable
       uinteger-sinteger-bit-roles-wfp-of-integer-format-inc-sign-tcnpnt
       posp))))

  (defruled integer-format->bit-size-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size)
                  (not (equal size 1)))
             (equal (integer-format->bit-size (integer-format-inc-sign-tcnpnt size))
                    size))
    :enable (integer-format->bit-size
             uinteger-format-inc-npnt
             sinteger-format-inc-sign-tcnpnt
             uinteger-sinteger-bit-roles-wfp-of-inc-n-and-sign
             sinteger-bit-roles-wfp-of-sinteger-bit-roles-inc-n-and-sign
             posp))

  (defruled integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size)
                  (not (equal size 1)))
             (equal (integer-format->unsigned-max
                     (integer-format-inc-sign-tcnpnt size))
                    (1- (expt 2 size))))
    :enable (integer-format->unsigned-max
             uinteger-format->max-of-uinteger-format-inc-npnt
             uinteger-sinteger-bit-roles-wfp-of-integer-format-inc-sign-tcnpnt))

  (defruled integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size)
                  (not (equal size 1)))
             (equal (integer-format->signed-max
                     (integer-format-inc-sign-tcnpnt size))
                    (1- (expt 2 (1- size)))))
    :enable (integer-format->signed-max
             sinteger-format->max-of-sinteger-format-inc-sign-tcnpnt
             uinteger-sinteger-bit-roles-wfp-of-integer-format-inc-sign-tcnpnt
             posp))

  (defruled integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size)
                  (not (equal size 1)))
             (equal (integer-format->signed-min
                     (integer-format-inc-sign-tcnpnt size))
                    (- (expt 2 (1- size)))))
    :enable (integer-format->signed-min
             sinteger-format->min-of-sinteger-format-inc-sign-tcnpnt
             uinteger-sinteger-bit-roles-wfp-of-integer-format-inc-sign-tcnpnt
             posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format-short-wfp ((short-format integer-formatp)
                                  (uchar-format uchar-formatp)
                                  (schar-format schar-formatp))
  :returns (yes/no booleanp)
  :short "Check if an integer format is well-formed
          when used for (signed and unsigned) @('short')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of bits must be a multiple of @('CHAR_BIT') [C17:6.2.6.1/4].")
   (xdoc::p
    "The possible signed values must cover at least
     the range from -32767 to +32767 (both inclusive) [C17:5.2.4.2.1/1].
     The possible unsigned values must cover at least
     the range from 0 to 65535 (both inclusive) [C17:5.2.4.2.1/1].")
   (xdoc::p
    "The possible signed values must at least include
     those of @('signed char'),
     and the possible unsigned values must at least include
     those of @('unsigned char')
     [C17:6.2.5/8]."))
  (b* ((bit-size (integer-format->bit-size short-format))
       (signed-short-min (integer-format->signed-min short-format))
       (signed-short-max (integer-format->signed-max short-format))
       (unsigned-short-max (integer-format->unsigned-max short-format))
       (signed-char-min (schar-format->min schar-format uchar-format))
       (signed-char-max (schar-format->max schar-format uchar-format))
       (unsigned-char-max (uchar-format->max uchar-format)))
    (and (integerp (/ bit-size (uchar-format->size uchar-format)))
         (<= signed-short-min -32767)
         (<= +32767 signed-short-max)
         (<= 65535 unsigned-short-max)
         (<= signed-short-min signed-char-min)
         (<= signed-char-max signed-short-max)
         (<= unsigned-char-max unsigned-short-max)))
  :hooks (:fix)

  ///

  (defrule integer-format-short-wf-bit-size-lower-bound
    (implies (integer-format-short-wfp short-format uchar-format schar-fomat)
             (>= (integer-format->bit-size short-format)
                 16))
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance integer-format->unsigned-max-upper-bound
                             (format short-format))
             :in-theory (disable integer-format->unsigned-max-upper-bound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format-int-wfp ((int-format integer-formatp)
                                (uchar-format uchar-formatp)
                                (short-format integer-formatp))
  :returns (yes/no booleanp)
  :short "Check if an integer format is well-formed
          when used for (signed and unsigned) @('int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of bits must be a multiple of @('CHAR_BIT') [C17:6.2.6.1/4].")
   (xdoc::p
    "The possible signed values must cover at least
     the range from -32767 to +32767 (both inclusive) [C17:5.2.4.2.1/1].
     The possible unsigned values must cover at least
     the range from 0 to 65535 (both inclusive) [C17:5.2.4.2.1/1].")
   (xdoc::p
    "The possible signed values must at least include
     those of @('signed short'),
     and the possible unsigned values must at least include
     those of @('unsigned short')
     [C17:6.2.5/8]."))
  (b* ((bit-size (integer-format->bit-size int-format))
       (signed-int-min (integer-format->signed-min int-format))
       (signed-int-max (integer-format->signed-max int-format))
       (unsigned-int-max (integer-format->unsigned-max int-format))
       (signed-short-min (integer-format->signed-min short-format))
       (signed-short-max (integer-format->signed-max short-format))
       (unsigned-short-max (integer-format->unsigned-max short-format)))
    (and (integerp (/ bit-size (uchar-format->size uchar-format)))
         (<= signed-int-min -32767)
         (<= +32767 signed-int-max)
         (<= 65535 unsigned-int-max)
         (<= signed-int-min signed-short-min)
         (<= signed-short-max signed-int-max)
         (<= unsigned-short-max unsigned-int-max)))
  :hooks (:fix)

  ///

  (defrule integer-format-int-wf-bit-size-lower-bound
    (implies (integer-format-int-wfp int-format uchar-format short-fomat)
             (>= (integer-format->bit-size int-format)
                 16))
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance integer-format->unsigned-max-upper-bound
                             (format int-format))
             :in-theory (disable integer-format->unsigned-max-upper-bound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format-long-wfp ((long-format integer-formatp)
                                 (uchar-format uchar-formatp)
                                 (int-format integer-formatp))
  :returns (yes/no booleanp)
  :short "Check if an integer format is well-formed
          when used for (signed and unsigned) @('long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of bits must be a multiple of @('CHAR_BIT') [C17:6.2.6.1/4].")
   (xdoc::p
    "The possible signed values must cover at least
     the range from -2147483647 to +2147483647 (both inclusive)
     [C17:5.2.4.2.1/1].
     The possible unsigned values must cover at least
     the range from 0 to 4294967295 (both inclusive) [C17:5.2.4.2.1/1].")
   (xdoc::p
    "The possible signed values must at least include
     those of @('signed int'),
     and the possible unsigned values must at least include
     those of @('unsigned int')
     [C17:6.2.5/8]."))
  (b* ((bit-size (integer-format->bit-size long-format))
       (signed-long-min (integer-format->signed-min long-format))
       (signed-long-max (integer-format->signed-max long-format))
       (unsigned-long-max (integer-format->unsigned-max long-format))
       (signed-int-min (integer-format->signed-min int-format))
       (signed-int-max (integer-format->signed-max int-format))
       (unsigned-int-max (integer-format->unsigned-max int-format)))
    (and (integerp (/ bit-size (uchar-format->size uchar-format)))
         (<= signed-long-min -2147483647)
         (<= +2147483647 signed-long-max)
         (<= 4294967295 unsigned-long-max)
         (<= signed-long-min signed-int-min)
         (<= signed-int-max signed-long-max)
         (<= unsigned-int-max unsigned-long-max)))
  :hooks (:fix)

  ///

  (defrule integer-format-long-wf-bit-size-lower-bound
    (implies (integer-format-long-wfp long-format uchar-format int-fomat)
             (>= (integer-format->bit-size long-format)
                 32))
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance integer-format->unsigned-max-upper-bound
                             (format long-format))
             :in-theory (disable integer-format->unsigned-max-upper-bound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-format-llong-wfp ((llong-format integer-formatp)
                                  (uchar-format uchar-formatp)
                                  (long-format integer-formatp))
  :returns (yes/no booleanp)
  :short "Check if an integer format is well-formed
          when used for (signed and unsigned) @('long long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of bits must be a multiple of @('CHAR_BIT') [C17:6.2.6.1/4].")
   (xdoc::p
    "The possible signed values must cover at least
     the range from -9223372036854775807 to +9223372036854775807
     (both inclusive) [C17:5.2.4.2.1/1].
     The possible unsigned values must cover at least
     the range from 0 to 18446744073709551615 (both inclusive)
     [C17:5.2.4.2.1/1].")
   (xdoc::p
    "The possible signed values must at least include
     those of @('signed long'),
     and the possible unsigned values must at least include
     those of @('unsigned long')
     [C17:6.2.5/8]."))
  (b* ((bit-size (integer-format->bit-size llong-format))
       (signed-llong-min (integer-format->signed-min llong-format))
       (signed-llong-max (integer-format->signed-max llong-format))
       (unsigned-llong-max (integer-format->unsigned-max llong-format))
       (signed-long-min (integer-format->signed-min long-format))
       (signed-long-max (integer-format->signed-max long-format))
       (unsigned-long-max (integer-format->unsigned-max long-format)))
    (and (integerp (/ bit-size (uchar-format->size uchar-format)))
         (<= signed-llong-min -9223372036854775807)
         (<= +9223372036854775807 signed-llong-max)
         (<= 18446744073709551615 unsigned-llong-max)
         (<= signed-llong-min signed-long-min)
         (<= signed-long-max signed-llong-max)
         (<= unsigned-long-max unsigned-llong-max)))
  :hooks (:fix)

  ///

  (defrule integer-format-llong-wf-bit-size-lower-bound
    (implies (integer-format-llong-wfp llong-format uchar-format long-fomat)
             (>= (integer-format->bit-size llong-format)
                 64))
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance integer-format->unsigned-max-upper-bound
                             (format llong-format))
             :in-theory (disable integer-format->unsigned-max-upper-bound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-format-short/int/long/llong-wfp-of-inc-sign-tcnpnt
  :short "Theorems about the well-formedness of
          @('short')s, @('int')s, @('long')s, and @('long long')s
          specified via @(tsee integer-format-inc-sign-tcnpnt)."
  :long
  (xdoc::topstring
   (xdoc::p
    "When these integer formats are specified
     via @(tsee integer-format-inc-sign-tcnpnt),
     their well-formedness reduces to
     simple conditions on the sizes."))

  (defruled integer-format-short-wfp-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size)
                  (not (equal size 1)))
             (equal (integer-format-short-wfp
                     (integer-format-inc-sign-tcnpnt size)
                     uchar-format
                     schar-format)
                    (and (integerp (/ size (uchar-format->size uchar-format)))
                         (>= size 16)
                         (>= size (uchar-format->size uchar-format)))))
    :enable (integer-format-short-wfp
             integer-format->bit-size-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt
             schar-format->min
             schar-format->max
             uchar-format->max)
    :use ((:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 15)
                     (n (1- size))
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 16)
                     (n size)
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m (uchar-format->size uchar-format))
                     (n size)
                     (x 2)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1
    :prep-books ((acl2::scatter-exponents)))

  (defruled integer-format-int-wfp-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size0)
                  (not (equal size0 1))
                  (posp size)
                  (not (equal size 1)))
             (equal (integer-format-int-wfp
                     (integer-format-inc-sign-tcnpnt size)
                     uchar-format
                     (integer-format-inc-sign-tcnpnt size0))
                    (and (integerp (/ size (uchar-format->size uchar-format)))
                         (>= size 16)
                         (>= size size0))))
    :enable (integer-format-int-wfp
             integer-format->bit-size-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt)
    :use ((:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 15)
                     (n (1- size))
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 16)
                     (n size)
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m size0)
                     (n size)
                     (x 2)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1
    :prep-books ((acl2::scatter-exponents)))

  (defruled integer-format-long-wfp-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size0)
                  (not (equal size0 1))
                  (posp size)
                  (not (equal size 1)))
             (equal (integer-format-long-wfp
                     (integer-format-inc-sign-tcnpnt size)
                     uchar-format
                     (integer-format-inc-sign-tcnpnt size0))
                    (and (integerp (/ size (uchar-format->size uchar-format)))
                         (>= size 32)
                         (>= size size0))))
    :enable (integer-format-long-wfp
             integer-format->bit-size-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt)
    :use ((:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 31)
                     (n (1- size))
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 32)
                     (n size)
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m size0)
                     (n size)
                     (x 2)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1
    :prep-books ((acl2::scatter-exponents)))

  (defruled integer-format-llong-wfp-of-integer-format-inc-sign-tcnpnt
    (implies (and (posp size0)
                  (not (equal size0 1))
                  (posp size)
                  (not (equal size 1)))
             (equal (integer-format-llong-wfp
                     (integer-format-inc-sign-tcnpnt size)
                     uchar-format
                     (integer-format-inc-sign-tcnpnt size0))
                    (and (integerp (/ size (uchar-format->size uchar-format)))
                         (>= size 64)
                         (>= size size0))))
    :enable (integer-format-llong-wfp
             integer-format->bit-size-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt)
    :use ((:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 63)
                     (n (1- size))
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m 64)
                     (n size)
                     (x 2))
          (:instance acl2::expt-is-weakly-increasing-for-base->-1
                     (m size0)
                     (n size)
                     (x 2)))
    :disable acl2::expt-is-weakly-increasing-for-base->-1
    :prep-books ((acl2::scatter-exponents))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-format-16tcnt ()
  :returns (format integer-formatp)
  :short "The (@('unsigned') and @('signed')) @('short') format defined by
          16 bits with increasing values,
          two's complement,
          and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and smallest format for @('short') integers,
     with two's complement being the most common signed format.
     There cannot be any padding bits,
     otherwise the value bits would not suffice to cover
     the required ranges of values.
     With no padding bits, there is only one possible trap representation,
     namely the one with sign bit 1 and all value bits 0,
     but the simplest and most common choice is that it is a valid value instead
     (the smallest signed value representable in the type)."))
  (integer-format-inc-sign-tcnpnt 16)

  ///

  (defrule integer-format-short-wfp-of-short-format-16tcnt
    (integer-format-short-wfp (short-format-16tcnt)
                              (uchar-format-8)
                              (schar-format-8tcnt)))

  (defruled integer-format->bit-size-of-short-format-16tcnt
    (equal (integer-format->bit-size (short-format-16tcnt))
           16))

  (defruled uinteger-format->max-of-short-format-16tcnt
    (equal (uinteger-format->max
            (uinteger+sinteger-format->unsigned
             (integer-format->pair
              (short-format-16tcnt))))
           65535))

  (defruled sinteger-format->max-of-short-format-16tcnt
    (equal (sinteger-format->max
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (short-format-16tcnt))))
           32767))

  (defruled sinteger-format->min-of-short-format-16tcnt
    (equal (sinteger-format->min
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (short-format-16tcnt))))
           -32768)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-format-16tcnt ()
  :returns (format integer-formatp)
  :short "The (@('unsigned') and @('signed')) @('int') format defined by
          16 bits with increasing values,
          two's complement,
          and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and smallest format for @('int') integers,
     with two's complement being the most common signed format.
     There cannot be any padding bits,
     otherwise the value bits would not suffice to cover
     the required ranges of values.
     With no padding bits, there is only one possible trap representation,
     namely the one with sign bit 1 and all value bits 0,
     but the simplest and most common choice is that it is a valid value instead
     (the smallest signed value representable in the type)."))
  (integer-format-inc-sign-tcnpnt 16)

  ///

  (defrule integer-format-int-wfp-of-int-format-16tcnt
    (integer-format-int-wfp (int-format-16tcnt)
                            (uchar-format-8)
                            (short-format-16tcnt)))

  (defruled integer-format->bit-size-of-int-format-16tcnt
    (equal (integer-format->bit-size (int-format-16tcnt))
           16))

  (defruled uinteger-format->max-of-int-format-16tcnt
    (equal (uinteger-format->max
            (uinteger+sinteger-format->unsigned
             (integer-format->pair
              (int-format-16tcnt))))
           65535))

  (defruled sinteger-format->max-of-int-format-16tcnt
    (equal (sinteger-format->max
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (int-format-16tcnt))))
           32767))

  (defruled sinteger-format->min-of-int-format-16tcnt
    (equal (sinteger-format->min
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (int-format-16tcnt))))
           -32768)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-format-32tcnt ()
  :returns (format integer-formatp)
  :short "The (@('unsigned') and @('signed')) @('long') format defined by
          32 bits with increasing values,
          two's complement,
          and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and smallest format for @('long') integers,
     with two's complement being the most common signed format.
     There cannot be any padding bits,
     otherwise the value bits would not suffice to cover
     the required ranges of values.
     With no padding bits, there is only one possible trap representation,
     namely the one with sign bit 1 and all value bits 0,
     but the simplest and most common choice is that it is a valid value instead
     (the smallest signed value representable in the type)."))
  (integer-format-inc-sign-tcnpnt 32)

  ///

  (defrule integer-format-long-wfp-of-long-format-32tcnt
    (integer-format-long-wfp (long-format-32tcnt)
                             (uchar-format-8)
                             (int-format-16tcnt)))

  (defruled integer-format->bit-size-of-long-format-32tcnt
    (equal (integer-format->bit-size (long-format-32tcnt))
           32))

  (defruled uinteger-format->max-of-long-format-32tcnt
    (equal (uinteger-format->max
            (uinteger+sinteger-format->unsigned
             (integer-format->pair
              (long-format-32tcnt))))
           4294967295))

  (defruled sinteger-format->max-of-long-format-32tcnt
    (equal (sinteger-format->max
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (long-format-32tcnt))))
           2147483647))

  (defruled sinteger-format->min-of-long-format-32tcnt
    (equal (sinteger-format->min
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (long-format-32tcnt))))
           -2147483648)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define llong-format-64tcnt ()
  :returns (format integer-formatp)
  :short "The (@('unsigned') and @('signed')) @('long long') format defined by
          64 bits with increasing values,
          two's complement,
          and no trap representations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the simplest and smallest format for @('long long') integers,
     with two's complement being the most common signed format.
     There cannot be any padding bits,
     otherwise the value bits would not suffice to cover
     the required ranges of values.
     With no padding bits, there is only one possible trap representation,
     namely the one with sign bit 1 and all value bits 0,
     but the simplest and most common choice is that it is a valid value instead
     (the smallest signed value representable in the type)."))
  (integer-format-inc-sign-tcnpnt 64)

  ///

  (defrule integer-format-llong-wfp-of-long-format-64tcnt
    (integer-format-llong-wfp (llong-format-64tcnt)
                              (uchar-format-8)
                              (long-format-32tcnt)))

  (defruled integer-format->bit-size-of-llong-format-64tcnt
    (equal (integer-format->bit-size (llong-format-64tcnt))
           64))

  (defruled uinteger-format->max-of-llong-format-64tcnt
    (equal (uinteger-format->max
            (uinteger+sinteger-format->unsigned
             (integer-format->pair
              (llong-format-64tcnt))))
           18446744073709551615))

  (defruled sinteger-format->max-of-llong-format-64tcnt
    (equal (sinteger-format->max
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (llong-format-64tcnt))))
           9223372036854775807))

  (defruled sinteger-format->min-of-llong-format-64tcnt
    (equal (sinteger-format->min
            (uinteger+sinteger-format->signed
             (integer-format->pair
              (llong-format-64tcnt))))
           -9223372036854775808)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char+short+int+long+llong-format
  :short "Fixtype of formats of
          (unsigned, signed, and plain) @('char') objects,
          (unsigned and signed) @('short') objects,
          (unsigned and signed) @('int') objects,
          (unsigned and signed) @('long') objects, and
          (unsigned and signed) @('long long') objects."
  ((uchar uchar-format)
   (schar schar-format)
   (char char-format)
   (short integer-format)
   (int integer-format)
   (long integer-format)
   (llong integer-format))
  :pred char+short+int+long+llong-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char+short+int+long+llong-format-wfp
  ((format char+short+int+long+llong-formatp))
  :returns (yes/no booleanp)
  :short "Check if the formats of
          @('char'), @('short'), @('int'), @('long'), and @('long long') objects
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The formats for @('char') objects already include
     their own well-formedness in their definition.
     We impose well-formedness on the other formats."))
  (b* (((char+short+int+long+llong-format format) format))
    (and (integer-format-short-wfp format.short format.uchar format.schar)
         (integer-format-int-wfp format.int format.uchar format.short)
         (integer-format-long-wfp format.long format.uchar format.int)
         (integer-format-llong-wfp format.llong format.uchar format.long)))
  :hooks (:fix)

  ///

  (defrule char+short+int+long+llong-format-wf-short-bit-size-lower-bound
    (implies (char+short+int+long+llong-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong-format->short format))
                 16))
    :rule-classes :linear)

  (defrule char+short+int+long+llong-format-wf-int-bit-size-lower-bound
    (implies (char+short+int+long+llong-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong-format->int format))
                 16))
    :rule-classes :linear)

  (defrule char+short+int+long+llong-format-wf-long-bit-size-lower-bound
    (implies (char+short+int+long+llong-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong-format->long format))
                 32))
    :rule-classes :linear)

  (defrule char+short+int+long+llong-format-wf-llong-bit-size-lower-bound
    (implies (char+short+int+long+llong-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong-format->llong format))
                 64))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char8+short16+int16+long32+llong64-tcnt ()
  :short "The @('char'), @('short'), @('int'), @('long'), and @('long long')
          integer formats defined by
          the minimal number of bits with increasing values,
          two's complement,
          no trap representations, and
          unsigned plain @('char')s."
  (make-char+short+int+long+llong-format
   :uchar (uchar-format-8)
   :schar (schar-format-8tcnt)
   :char (char-format-8u)
   :short (short-format-16tcnt)
   :int (int-format-16tcnt)
   :long (long-format-32tcnt)
   :llong (llong-format-64tcnt))

  ///

  (defruled wfp-of-char8+short16+int16+long32+llong64-tcnt
    (char+short+int+long+llong-format-wfp
     (char8+short16+int16+long32+llong64-tcnt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ienv
  :short "Fixtype of implementation environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this only contains the following information:")
   (xdoc::ul
    (xdoc::li
     "The formats of the three character types.")
    (xdoc::li
     "The formats of the standard signed integer types
      and their unsigned counterparts.")
    (xdoc::li
     "A flag saying whether the GCC extensions are enabled or not."))
   (xdoc::p
    "We plan to add more information.")
   (xdoc::p
    "The reason for using
     the ``intermediate'' fixtype @(tsee char+short+int+long+llong-format)
     is the same as explained in @(tsee integer-format)
     about the ``intermediate'' fixtype used there.
     We may eliminate this at some point.")
   (xdoc::p
    "The GCC flag could evolve into a rich set of C versions."))
  ((char+short+int+long+llong-format
    char+short+int+long+llong-format
    :reqfix (if (char+short+int+long+llong-format-wfp
                 char+short+int+long+llong-format)
                char+short+int+long+llong-format
              (char8+short16+int16+long32+llong64-tcnt)))
   (gcc bool))
  :require (char+short+int+long+llong-format-wfp
            char+short+int+long+llong-format)
  :pred ienvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-size ((ienv ienvp))
  :returns (size posp)
  :short "The ACL2 integer value of @('CHAR_BIT') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the size, in bits, of
     (possibly @('unsigned') or @('signed')) @('char') objects."))
  (uchar-format->size
   (char+short+int+long+llong-format->uchar
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)
  ///

  (defret ienv->char-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->char-size-lower-bound
    (>= size 8)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uchar-max ((ienv ienvp))
  :returns (max posp :hints (("Goal" :in-theory (enable posp))))
  :short "The ACL2 integer value of @('UCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee uchar-format->max)."))
  (uchar-format->max
   (char+short+int+long+llong-format->uchar
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)
  ///

  (defret ienv->uchar-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

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
    "See @(tsee schar-format->max)."))
  (schar-format->max
   (char+short+int+long+llong-format->schar
    (ienv->char+short+int+long+llong-format ienv))
   (char+short+int+long+llong-format->uchar
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)
  ///

  (defret ienv->schar-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

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
    "See @(tsee schar-format->min)"))
  (schar-format->min
   (char+short+int+long+llong-format->schar
    (ienv->char+short+int+long+llong-format ienv))
   (char+short+int+long+llong-format->uchar
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)
  ///

  (defret ienv->schar-min-type-prescription
    (and (integerp min)
         (< min 0))
    :rule-classes :type-prescription)

  (defret ienv->schar-min-upper-bound
    (<= min -127)
    :rule-classes ((:linear :trigger-terms ((ienv->schar-min ienv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-max ((ienv ienvp))
  :returns (max integerp)
  :short "The ACL2 integer value of @('CHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee char-format->max)."))
  (char-format->max
   (char+short+int+long+llong-format->char
    (ienv->char+short+int+long+llong-format ienv))
   (char+short+int+long+llong-format->uchar
    (ienv->char+short+int+long+llong-format ienv))
   (char+short+int+long+llong-format->schar
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)
  ///

  (defret ienv->char-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

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
    "See @(tsee char-format->min)."))
  (char-format->min
   (char+short+int+long+llong-format->char
    (ienv->char+short+int+long+llong-format ienv))
   (char+short+int+long+llong-format->uchar
    (ienv->char+short+int+long+llong-format ienv))
   (char+short+int+long+llong-format->schar
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)
  ///

  (defret ienv->char-min-type-prescription
    (and (integerp min)
         (<= min 0))
    :rule-classes :type-prescription)

  (defret ienv->char-min-upper-bound
    (<= min 0)
    :rule-classes ((:linear :trigger-terms ((ienv->char-min ienv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->short-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('short') objects."
  (integer-format->bit-size
   (char+short+int+long+llong-format->short
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)

  ///

  (defret ienv->short-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->short-bit-size-lower-bound
    (>= size 16)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->short-byte-size ((ienv ienvp))
  :returns (size posp
                 :hints (("Goal"
                          :in-theory (e/d (posp
                                           char+short+int+long+llong-format-wfp
                                           integer-format-short-wfp
                                           ienv->char-size
                                           ienv->short-bit-size)
                                          (ienv-requirements))
                          :use (:instance ienv-requirements (x ienv))
                         )))
  :short "Number of bytes of unsigned and signed @('short') objects."
  (/ (ienv->short-bit-size ienv)
     (ienv->char-size ienv))
  :hooks (:fix)

  ///

  (defret ienv->short-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    ::hints (("Goal" :in-theory (disable ienv->short-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->int-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('int') objects."
  (integer-format->bit-size
   (char+short+int+long+llong-format->int
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)

  ///

  (defret ienv->int-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->int-bit-size-lower-bound
    (>= size 16)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->int-byte-size ((ienv ienvp))
  :returns (size posp
                 :hints (("Goal"
                          :in-theory (e/d (posp
                                           char+short+int+long+llong-format-wfp
                                           integer-format-int-wfp
                                           ienv->char-size
                                           ienv->int-bit-size)
                                          (ienv-requirements))
                          :use (:instance ienv-requirements (x ienv))
                         )))
  :short "Number of bytes of unsigned and signed @('int') objects."
  (/ (ienv->int-bit-size ienv)
     (ienv->char-size ienv))
  :hooks (:fix)

  ///

  (defret ienv->int-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    ::hints (("Goal" :in-theory (disable ienv->int-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->long-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('long') objects."
  (integer-format->bit-size
   (char+short+int+long+llong-format->long
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)

  ///

  (defret ienv->long-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->long-bit-size-lower-bound
    (>= size 32)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->long-byte-size ((ienv ienvp))
  :returns (size posp
                 :hints (("Goal"
                          :in-theory (e/d (posp
                                           char+short+int+long+llong-format-wfp
                                           integer-format-long-wfp
                                           ienv->char-size
                                           ienv->long-bit-size)
                                          (ienv-requirements))
                          :use (:instance ienv-requirements (x ienv))
                         )))
  :short "Number of bytes of unsigned and signed @('long') objects."
  (/ (ienv->long-bit-size ienv)
     (ienv->char-size ienv))
  :hooks (:fix)

  ///

  (defret ienv->long-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    ::hints (("Goal" :in-theory (disable ienv->long-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->llong-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('long long') objects."
  (integer-format->bit-size
   (char+short+int+long+llong-format->llong
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix)

  ///

  (defret ienv->llong-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->llong-bit-size-lower-bound
    (>= size 64)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->llong-byte-size ((ienv ienvp))
  :returns (size posp
                 :hints (("Goal"
                          :in-theory (e/d (posp
                                           char+short+int+long+llong-format-wfp
                                           integer-format-llong-wfp
                                           ienv->char-size
                                           ienv->llong-bit-size)
                                          (ienv-requirements))
                          :use (:instance ienv-requirements (x ienv))
                         )))
  :short "Number of bytes of unsigned and signed @('long long') objects."
  (/ (ienv->llong-bit-size ienv)
     (ienv->char-size ienv))
  :hooks (:fix)

  ///

  (defret ienv->llong-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    ::hints (("Goal" :in-theory (disable ienv->llong-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ushort-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('USHRT_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max
   (char+short+int+long+llong-format->short
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sshort-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('SHRT_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max
   (char+short+int+long+llong-format->short
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sshort-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('SHRT_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min
   (char+short+int+long+llong-format->short
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uint-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('UINT_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max
   (char+short+int+long+llong-format->int
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sint-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('INT_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max
   (char+short+int+long+llong-format->int
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sint-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('INT_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min
   (char+short+int+long+llong-format->int
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ulong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('ULONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max
   (char+short+int+long+llong-format->long
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->slong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('LONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max
   (char+short+int+long+llong-format->long
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->slong-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('LONG_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min
   (char+short+int+long+llong-format->long
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ullong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('ULLONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max
   (char+short+int+long+llong-format->llong
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sllong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('LLONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max
   (char+short+int+long+llong-format->llong
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sllong-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('LLONG_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min
   (char+short+int+long+llong-format->llong
    (ienv->char+short+int+long+llong-format ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uchar-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned char')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uchar-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-schar-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed char')."
  (and (<= (ienv->schar-min ienv) (ifix val))
       (<= (ifix val) (ienv->schar-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-char-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('char')."
  (and (<= (ienv->char-min ienv) (ifix val))
       (<= (ifix val) (ienv->char-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ushort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned short')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ushort-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sshort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed short')."
  (and (<= (ienv->sshort-min ienv) (ifix val))
       (<= (ifix val) (ienv->sshort-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned int')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uint-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed int')."
  (and (<= (ienv->sint-min ienv) (ifix val))
       (<= (ifix val) (ienv->sint-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ulong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ulong-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-slong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed long')."
  (and (<= (ienv->slong-min ienv) (ifix val))
       (<= (ifix val) (ienv->slong-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ullong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned long long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ullong-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sllong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed long long')."
  (and (<= (ienv->sllong-min ienv) (ifix val))
       (<= (ifix val) (ienv->sllong-max ienv)))
  :hooks (:fix))
