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

(include-book "uchar-formats")
(include-book "signed-formats")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ schar-formats
  :parents (implementation-environments)
  :short "Formats of @('signed char') objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the possible formats of @('signed char') objects,
     along with some operations on them."))
  :order-subtopics t
  :default-parent t)

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
