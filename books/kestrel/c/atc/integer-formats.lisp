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
  :parents (atc-implementation)
  :short "C integer formats for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C] provides constraints on the formats of
     the (non-extended) integer types [C:6.2.5],
     but not a complete definition of the formats (unlike Java).
     A general formalization of C should be parameterized over these formats.
     Here, for the current purposes of ATC,
     we define the formats, but we do so in a way that
     should make it easy to change and swap some aspects of the definitions.")
   (xdoc::p
    "[C:6.2.6.2/2] allows padding bits,
     which we disallow here.
     [C:6.2.6.2/2] allows signed integers to be
     two's complement, one's complement, or sign and magnitude;
     we just assume two's complement here.
     The exact number of bits in a byte is also implementation-dependent
     [C:5.2.4.2.1/1] [C:6.2.6.1/3],
     but we just assume 8 bits here.
     Given all of these choices,
     the remaining choices can be described in terms of
     the number of bytes that form (signed and unsigned)
     @('short')s, @('int')s, @('long')s, and @('long long')s;
     note that each unsigned/signed integer type
     takes the same storage as the corresponding signed/unsigned type
     [C:6.2.5/6].")
   (xdoc::p
    "So here we introduce four nullary functions for these sizes in bytes.
     We prove some theorems about them but then disable their definitions,
     including their executable counterparts.
     This way, we minimize the dependencies from the exact definitions,
     and we try and define the integer values and operations
     as independently from the exact sizes as possible.
     This way, it should not be difficult to replace this file
     with another one with different definitions.")
   (xdoc::p
    "The definitions that we pick here are consistent with @('gcc')
     on (at least some versions of) macOS and Linux, namely:
     @('short') is 2 bytes,
     @('int') is 4 bytes,
     @('long') is 8 bytes, and
     @('long long') is also 8 bytes.
     These are all consistent with the ranges in [C:5.2.4.2.1]:
     @('short') is at least 2 bytes,
     @('int') is at least 2 bytes,
     @('long') is at least 4 bytes, and
     @('long long') is at least 8 bytes.
     Furthermore, the ranges are increasing [C:6.2.5/8]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-bytes ()
  :returns (short-bytes posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('short')s, in bytes."
  2
  ///

  (in-theory (disable (:e short-bytes)))

  (defret short-bytes-bound
    (>= short-bytes 2)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-bytes ()
  :returns (int-bytes posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('int')s, in bytes."
  4
  ///

  (in-theory (disable (:e int-bytes)))

  (defret int-bytes-bound
    (>= int-bytes 2)
    :rule-classes :linear)

  (defrule int-bytes->=-short-bytes
    (>= (int-bytes) (short-bytes))
    :rule-classes :linear
    :enable short-bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-bytes ()
  :returns (long-bytes posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('long')s, in bytes."
  8
  ///

  (in-theory (disable (:e long-bytes)))

  (defret long-bytes-bound
    (>= long-bytes 4)
    :rule-classes :linear)

  (defrule long-bytes->=-int-bytes
    (>= (long-bytes) (int-bytes))
    :rule-classes :linear
    :enable int-bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define llong-bytes ()
  :returns (llong-bytes posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('long long')s, in bytes."
  8
  ///

  (in-theory (disable (:e llong-bytes)))

  (defret llong-bytes-bound
    (>= llong-bytes 8)
    :rule-classes :linear)

  (defrule llong-bytes->=-long-bytes
    (>= (llong-bytes) (long-bytes))
    :rule-classes :linear
    :enable long-bytes))
