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
(include-book "schar-formats")
(include-book "char-formats")
(include-book "bool-formats")
(include-book "integer-format-templates")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-formats
  :parents (implementation-environments)
  :short "Formats of integer objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the templates formalized in @(see integer-format-templates)
     to formalize the possible formats of the integer types
     other than @('unsigned'), @('signed'), and plain @('char') types,
     namely @('short'), @('int'), and larger types.
     We also put these together with
     our formalization of the possible formats of
     the @('unsigned'), @('signed'), and plain @('char') types,
     to form data structures for the possible formats of most integer types
     (we plan to add the remaining ones at some point)."))
  :order-subtopics t
  :default-parent t)

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

(fty::defprod char+short+int+long+llong+bool-format
  :short "Fixtype of formats of
          (unsigned, signed, and plain) @('char') objects,
          (unsigned and signed) @('short') objects,
          (unsigned and signed) @('int') objects,
          (unsigned and signed) @('long') objects,
          (unsigned and signed) @('long long') objects, and
          @('_Bool') objects."
  ((uchar uchar-format)
   (schar schar-format)
   (char char-format)
   (short integer-format)
   (int integer-format)
   (long integer-format)
   (llong integer-format)
   (bool bool-format))
  :pred char+short+int+long+llong+bool-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char+short+int+long+llong+bool-format-wfp
  ((format char+short+int+long+llong+bool-formatp))
  :returns (yes/no booleanp)
  :short "Check if the formats of
          @('char'),
          @('short'),
          @('int'),
          @('long'),
          @('long long'),
          and @('_Bool')
          objects
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The formats for @('char') objects already include
     their own well-formedness in their definition.
     We impose well-formedness on the other formats."))
  (b* (((char+short+int+long+llong+bool-format format) format))
    (and (integer-format-short-wfp format.short format.uchar format.schar)
         (integer-format-int-wfp format.int format.uchar format.short)
         (integer-format-long-wfp format.long format.uchar format.int)
         (integer-format-llong-wfp format.llong format.uchar format.long)
         (bool-format-wfp format.bool format.uchar)))
  :hooks (:fix)

  ///

  (defrule char+short+int+long+llong+bool-format-wf-short-bit-size-lower-bound
    (implies (char+short+int+long+llong+bool-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong+bool-format->short format))
                 16))
    :rule-classes :linear)

  (defrule char+short+int+long+llong+bool-format-wf-int-bit-size-lower-bound
    (implies (char+short+int+long+llong+bool-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong+bool-format->int format))
                 16))
    :rule-classes :linear)

  (defrule char+short+int+long+llong+bool-format-wf-long-bit-size-lower-bound
    (implies (char+short+int+long+llong+bool-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong+bool-format->long format))
                 32))
    :rule-classes :linear)

  (defrule char+short+int+long+llong+bool-format-wf-llong-bit-size-lower-bound
    (implies (char+short+int+long+llong+bool-format-wfp format)
             (>= (integer-format->bit-size
                  (char+short+int+long+llong+bool-format->llong format))
                 64))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char8+short16+int16+long32+llong64+bool0-tcnt ()
  :short "The
          @('char'),
          @('short'),
          @('int'),
          @('long'),
          @('long long'), and
          @('_Bool')
          integer formats defined by
          the minimal number of bits with increasing values,
          two's complement,
          no trap representations,
          unsigned plain @('char')s,
          and one-byte @('_Bool') objects
          with value in the least significant bit."
  (make-char+short+int+long+llong+bool-format
   :uchar (uchar-format-8)
   :schar (schar-format-8tcnt)
   :char (char-format-8u)
   :short (short-format-16tcnt)
   :int (int-format-16tcnt)
   :long (long-format-32tcnt)
   :llong (llong-format-64tcnt)
   :bool (bool-format-lsb))

  ///

  (defruled wfp-of-char8+short16+int16+long32+llong64+bool0-tcnt
    (char+short+int+long+llong+bool-format-wfp
     (char8+short16+int16+long32+llong64+bool0-tcnt))))
