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

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-formats
  :parents (atc-integers)
  :short "C integer formats for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C] provides constraints on the formats of the integer types [C:6.2.5],
     but not a complete definition of the formats (unlike Java).
     A general formalization of C should be parameterized over these formats.
     Here, for the current purposes of ATC,
     we define the formats, but we do so in a way that
     should make it easy to change and swap some aspects of the definitions.")
   (xdoc::p
    "[C:6.2.6.2/2] allows padding bits, which we disallow here.
     [C:6.2.6.2/2] allows signed integers to be
     two's complement, one's complement, or sign and magnitude;
     we just assume two's complement here.")
   (xdoc::p
    "The exact number of bits in a byte is also implementation-dependent
     [C:5.2.4.2.1/1] [C:6.2.6.1/3],
     so we introduce a nullary function for the number of bits in a byte,
     i.e. in a @('char') (unsigned, signed, or plain).
     We define it to be 8, because that ought to be the most frequent case.")
   (xdoc::p
    "We also introduce nullary functions for the number of bits that form
     (signed and unsigned)
     @('short')s, @('int')s, @('long'), and @('long long')s.
     Given the above choice of no padding bits,
     these numbers of bits have to be multiples of the number of bits in a byte,
     because those integers have to take a whole number of bytes.
     Recall that each unsigned/signed integer type
     takes the same storage as the corresponding signed/unsigned type
     [C:6.2.5/6].")
   (xdoc::p
    "We prove some theorems about the nullary functions.
     We disable their definitions, including executable counterparts.
     This way, we minimize the dependencies from the exact definitions,
     and we try and define the integer values and operations
     as independently from the exact sizes as possible.
     Thus, it may not be difficult to replace this file
     with another one with different definitions.")
   (xdoc::p
    "The definitions that we pick here are consistent with @('gcc')
     on (at least some versions of) macOS and Linux, namely:
     @('char') is 8 bits,
     @('short') is 16 bits (2 bytes),
     @('int') is 32 bits (4 bytes),
     @('long') is 64 bits (8 bytes), and
     @('long long') is also 64 bits (8 bytes).
     These are all consistent with the ranges in [C:5.2.4.2.1]:
     @('char') is at least 8 bits,
     @('short') is at least 16 bits,
     @('int') is at least 16 bits,
     @('long') is at least 32 bits, and
     @('long long') is at least 64 bits.
     Furthermore, the ranges are increasing [C:6.2.5/8].")
   (xdoc::p
    "We do not include any extended integer types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-bits ()
  :returns (char-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned, signed, and plain @('char')s, in bites."
  8
  ///

  (in-theory (disable (:e char-bits)))

  (defret char-bits-bound
    (>= char-bits 8)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-bits ()
  :returns (short-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('short')s, in bits."
  16
  ///

  (defrule short-bits-multiple-of-char-bits
    (integerp (/ (short-bits) (char-bits)))
    :enable char-bits)

  (in-theory (disable (:e short-bits)))

  (defret short-bits-bound
    (>= short-bits 16)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-bits ()
  :returns (int-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('int')s, in bits."
  32
  ///

  (defrule int-bits-multiple-of-char-bits
    (integerp (/ (int-bits) (char-bits)))
    :enable char-bits)

  (in-theory (disable (:e int-bits)))

  (defret int-bits-bound
    (>= int-bits 16)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-bits ()
  :returns (long-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('long')s, in bits."
  64
  ///

  (defrule long-bits-multiple-of-char-bits
    (integerp (/ (long-bits) (char-bits)))
    :enable char-bits)

  (in-theory (disable (:e long-bits)))

  (defret long-bits-bound
    (>= long-bits 32)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define llong-bits ()
  :returns (llong-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('long long')s, in bits."
  64
  ///

  (defrule llong-bits-multiple-of-char-bits
    (integerp (/ (llong-bits) (char-bits)))
    :enable char-bits)

  (in-theory (disable (:e llong-bits)))

  (defret llong-bits-bound
    (>= llong-bits 64)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule char-bits-vs-short-bits
    :parents (char-bits short-bits)
    :short "Relation between @('char') and @('short') sizes."
    ,(if (= (char-bits) (short-bits))
         '(= (char-bits) (short-bits))
       '(< (char-bits) (short-bits)))
    :rule-classes :linear
    :enable (char-bits short-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule short-bits-vs-int-bits
    :parents (short-bits int-bits)
    :short "Relation between @('short') and @('int') sizes."
    ,(if (= (short-bits) (int-bits))
         '(= (short-bits) (int-bits))
       '(< (short-bits) (int-bits)))
    :rule-classes :linear
    :enable (short-bits int-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule int-bits-vs-long-bits
    :parents (int-bits long-bits)
    :short "Relation between @('int') and @('long') sizes."
    ,(if (= (int-bits) (long-bits))
         '(= (int-bits) (long-bits))
       '(< (int-bits) (long-bits)))
    :rule-classes :linear
    :enable (int-bits long-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule long-bits-vs-lllong-bits
    :parents (long-bits llong-bits)
    :short "Relation between @('long') and @('long long') sizes."
    ,(if (= (long-bits) (llong-bits))
         '(= (long-bits) (llong-bits))
       '(< (long-bits) (llong-bits)))
    :rule-classes :linear
    :enable (long-bits llong-bits)))
