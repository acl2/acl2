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

(include-book "integer-formats")

(include-book "kestrel/fty/defbyte" :dir :system)
(include-book "kestrel/fty/sbyte8" :dir :system)
(include-book "kestrel/fty/ubyte8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-values
  :parents (atc-implementation)
  :short "C integer values for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a model of the C standard signed and unsigned integer values,
     based on their "
    (xdoc::seetopic "atc-integer-formats" "format definitions")
    ". As mentioned there, the definitions of values we give here
     should still work if the format definitions are changed.")
   (xdoc::p
    "We also define @('unsigned char') and @('signed char') values,
     which do not depend on format definitions,
     because we hardwire them to be 8 bits.")
   (xdoc::p
    "Then, for each of @('short'), @('int'), @('long'), and @('long long'),
     we define a size in bits (i.e. the size in bytes multiplied by 8),
     prove some linear rules about them,
     define ACL2 unsigned and signed integers for them
     (via @(tsee fty::defbyte)), and
     define C values by wrapping those unsigned and signed integers.
     We also define maximum and (for signed) minimum integers,
     prove some linear rules about them,
     and prove rules that provide alternative definitions
     of the unsigned and signed integers in terms of minima and maxima.
     This way we have the ability to view the integer ranges
     as ACL2's @(tsee unsigned-byte-p) and @(tsee signed-byte-p) values,
     which is useful for bitwise operations,
     but also as plain integers in certain ranges,
     which may lead to simpler reasoning about ranges."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-bits ()
  :returns (short-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('short')s, in bits."
  (* 8 (short-bytes))
  ///

  (in-theory (disable (:e short-bits)))

  (defret short-bits-lower-bound
    (>= short-bits 16)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-bits ()
  :returns (int-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('int')s, in bits."
  (* 8 (int-bytes))
  ///

  (in-theory (disable (:e int-bits)))

  (defret int-bits-lower-bound
    (>= int-bits 16)
    :rule-classes :linear)

  (defrule int-bits->=-short-bits
    (>= (int-bits) (short-bits))
    :rule-classes :linear
    :enable short-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-bits ()
  :returns (long-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('long')s, in bits."
  (* 8 (long-bytes))
  ///

  (in-theory (disable (:e long-bits)))

  (defret long-bits-lower-bound
    (>= long-bits 32)
    :rule-classes :linear)

  (defrule long-bits->=-int-bits
    (>= (long-bits) (int-bits))
    :rule-classes :linear
    :enable int-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define llong-bits ()
  :returns (llong-bits posp :rule-classes :type-prescription)
  :short "Size of unsigned and signed @('long long')s, in bits."
  (* 8 (llong-bytes))
  ///

  (in-theory (disable (:e llong-bits)))

  (defret llong-bits-lower-bound
    (>= llong-bits 64)
    :rule-classes :linear)

  (defrule llong-bits->=-long-bits
    (>= (llong-bits) (long-bits))
    :rule-classes :linear
    :enable long-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte ushort-integer
  :short "Fixtype of ACL2 integers in the range of C @('unsigned short')s."
  :size (short-bits)
  :signed nil
  :pred ushort-integerp)

;;;;;;;;;;;;;;;;;;;;

(fty::defbyte sshort-integer
  :short "Fixtype of ACL2 integers in the range of C @('signed short')s."
  :size (short-bits)
  :signed t
  :pred sshort-integerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte uint-integer
  :short "Fixtype of ACL2 integers in the range of C @('unsigned int')s."
  :size (int-bits)
  :signed nil
  :pred uint-integerp)

;;;;;;;;;;;;;;;;;;;;

(fty::defbyte sint-integer
  :short "Fixtype of ACL2 integers in the range of C @('signed int')s."
  :size (int-bits)
  :signed t
  :pred sint-integerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte ulong-integer
  :short "Fixtype of ACL2 integers in the range of C @('unsigned long')s."
  :size (long-bits)
  :signed nil
  :pred ulong-integerp)

;;;;;;;;;;;;;;;;;;;;

(fty::defbyte slong-integer
  :short "Fixtype of ACL2 integers in the range of C @('signed long')s."
  :size (long-bits)
  :signed t
  :pred slong-integerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte ullong-integer
  :short "Fixtype of ACL2 integers in the range of C @('unsigned long long')s."
  :size (llong-bits)
  :signed nil
  :pred ullong-integerp)

;;;;;;;;;;;;;;;;;;;;

(fty::defbyte sllong-integer
  :short "Fixtype of ACL2 integers in the range of C @('signed long long')s."
  :size (llong-bits)
  :signed t
  :pred sllong-integerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ushort-max ()
  :returns (ushort-max integerp :rule-classes :type-prescription)
  :short "Maximum integer value of C @('unsigned short')s."
  (1- (expt 2 (short-bits)))
  ///

  (in-theory (disable (:e ushort-max)))

  (defrule ushort-max-lower-bound
    (>= (ushort-max) 65535)
    :rule-classes :linear
    :enable ushort-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 16) (n (short-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define sshort-min ()
  :returns (sshort-min integerp :rule-classes :type-prescription)
  :short "Minimum integer value of C @('signed short')s."
  (- (expt 2 (1- (short-bits))))
  ///

  (in-theory (disable (:e sshort-min)))

  (defrule sshort-min-upper-bound
    (<= (sshort-min) -32768)
    :rule-classes :linear
    :enable sshort-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (short-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define sshort-max ()
  :returns (sshort-max integerp :rule-classes :type-prescription)
  :short "Maximumm integer value of C @('signed short')s."
  (1- (expt 2 (1- (short-bits))))
  ///

  (in-theory (disable (:e sshort-max)))

  (defrule sshort-max-lower-bound
    (>= (sshort-max) 32767)
    :rule-classes :linear
    :enable sshort-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (short-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-max ()
  :returns (uint-max integerp :rule-classes :type-prescription)
  :short "Maximum integer value of C @('unsigned int')s."
  (1- (expt 2 (int-bits)))
  ///

  (in-theory (disable (:e uint-max)))

  (defrule uint-max-lower-bound
    (>= (uint-max) 65535)
    :rule-classes :linear
    :enable uint-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 16) (n (int-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule uint-max->=-ushort-max
    (>= (uint-max) (ushort-max))
    :rule-classes :linear
    :enable ushort-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (short-bits)) (n (int-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define sint-min ()
  :returns (sint-min integerp :rule-classes :type-prescription)
  :short "Minimum integer value of C @('signed int')s."
  (- (expt 2 (1- (int-bits))))
  ///

  (in-theory (disable (:e sint-min)))

  (defrule sint-min-upper-bound
    (<= (sint-min) -32768)
    :rule-classes :linear
    :enable sint-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (int-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule sint-min-<=-sshort-min
    (<= (sint-min) (sshort-min))
    :rule-classes :linear
    :enable sshort-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (short-bits)) (n (int-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define sint-max ()
  :returns (sint-max integerp :rule-classes :type-prescription)
  :short "Maximumm integer value of C @('signed int')s."
  (1- (expt 2 (1- (int-bits))))
  ///

  (in-theory (disable (:e sint-max)))

  (defrule sint-max-lower-bound
    (>= (sint-max) 32767)
    :rule-classes :linear
    :enable sint-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (int-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule sint-max->=-sshort-max
    (>= (sint-max) (sshort-max))
    :rule-classes :linear
    :enable sshort-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (short-bits)) (n (int-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ulong-max ()
  :returns (ulong-max integerp :rule-classes :type-prescription)
  :short "Maximum integer value of C @('unsigned long')s."
  (1- (expt 2 (long-bits)))
  ///

  (in-theory (disable (:e ulong-max)))

  (defrule ulong-max-lower-bound
    (>= (ulong-max) 65535)
    :rule-classes :linear
    :enable ulong-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 16) (n (long-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule ulong-max->=-uint-max
    (>= (ulong-max) (uint-max))
    :rule-classes :linear
    :enable uint-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (int-bits)) (n (long-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define slong-min ()
  :returns (slong-min integerp :rule-classes :type-prescription)
  :short "Minimum integer value of C @('signed long')s."
  (- (expt 2 (1- (long-bits))))
  ///

  (in-theory (disable (:e slong-min)))

  (defrule slong-min-upper-bound
    (<= (slong-min) -32768)
    :rule-classes :linear
    :enable slong-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (long-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule slong-min-<=-sint-min
    (<= (slong-min) (sint-min))
    :rule-classes :linear
    :enable sint-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (int-bits)) (n (long-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define slong-max ()
  :returns (slong-max integerp :rule-classes :type-prescription)
  :short "Maximumm integer value of C @('signed long')s."
  (1- (expt 2 (1- (long-bits))))
  ///

  (in-theory (disable (:e slong-max)))

  (defrule slong-max-lower-bound
    (>= (slong-max) 32767)
    :rule-classes :linear
    :enable slong-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (long-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule slong-max->=-sint-max
    (>= (slong-max) (sint-max))
    :rule-classes :linear
    :enable sint-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (int-bits)) (n (long-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ullong-max ()
  :returns (ullong-max integerp :rule-classes :type-prescription)
  :short "Maximum integer value of C @('unsigned long long')s."
  (1- (expt 2 (llong-bits)))
  ///

  (in-theory (disable (:e ullong-max)))

  (defrule ullong-max-lower-bound
    (>= (ullong-max) 65535)
    :rule-classes :linear
    :enable ullong-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 16) (n (llong-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule ullong-max->=-ulong-max
    (>= (ullong-max) (ulong-max))
    :rule-classes :linear
    :enable ulong-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (long-bits)) (n (llong-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define sllong-min ()
  :returns (sllong-min integerp :rule-classes :type-prescription)
  :short "Minimum integer value of C @('signed long long')s."
  (- (expt 2 (1- (llong-bits))))
  ///

  (in-theory (disable (:e sllong-min)))

  (defrule sllong-min-upper-bound
    (<= (sllong-min) -32768)
    :rule-classes :linear
    :enable sllong-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (llong-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule sllong-min-<=-slong-min
    (<= (sllong-min) (slong-min))
    :rule-classes :linear
    :enable slong-min
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (long-bits)) (n (llong-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

(define sllong-max ()
  :returns (sllong-max integerp :rule-classes :type-prescription)
  :short "Maximumm integer value of C @('signed long long')s."
  (1- (expt 2 (1- (llong-bits))))
  ///

  (in-theory (disable (:e sllong-max)))

  (defrule sllong-max-lower-bound
    (>= (sllong-max) 32767)
    :rule-classes :linear
    :enable sllong-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m 15) (n (1- (llong-bits))) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defrule sllong-max->=-slong-max
    (>= (sllong-max) (slong-max))
    :rule-classes :linear
    :enable slong-max
    :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
          (m (long-bits)) (n (llong-bits)) (x 2))
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ushort-integerp-alt-def
  :short "Alternative definition of @(tsee ushort-integerp) as integer range."
  (equal (ushort-integerp x)
         (and (integerp x)
              (<= 0 x)
              (<= x (ushort-max))))
  :enable (ushort-integerp ushort-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;

(defruled sshort-integerp-alt-def
  :short "Alternative definition of @(tsee sshort-integerp) as integer range."
  (equal (sshort-integerp x)
         (and (integerp x)
              (<= (sshort-min) x)
              (<= x (sshort-max))))
  :enable (sshort-integerp sshort-min sshort-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled uint-integerp-alt-def
  :short "Alternative definition of @(tsee uint-integerp) as integer range."
  (equal (uint-integerp x)
         (and (integerp x)
              (<= 0 x)
              (<= x (uint-max))))
  :enable (uint-integerp uint-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;

(defruled sint-integerp-alt-def
  :short "Alternative definition of @(tsee sint-integerp) as integer range."
  (equal (sint-integerp x)
         (and (integerp x)
              (<= (sint-min) x)
              (<= x (sint-max))))
  :enable (sint-integerp sint-min sint-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ulong-integerp-alt-def
  :short "Alternative definition of @(tsee ulong-integerp) as integer range."
  (equal (ulong-integerp x)
         (and (integerp x)
              (<= 0 x)
              (<= x (ulong-max))))
  :enable (ulong-integerp ulong-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;

(defruled slong-integerp-alt-def
  :short "Alternative definition of @(tsee slong-integerp) as integer range."
  (equal (slong-integerp x)
         (and (integerp x)
              (<= (slong-min) x)
              (<= x (slong-max))))
  :enable (slong-integerp slong-min slong-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ullong-integerp-alt-def
  :short "Alternative definition of @(tsee ullong-integerp) as integer range."
  (equal (ullong-integerp x)
         (and (integerp x)
              (<= 0 x)
              (<= x (ullong-max))))
  :enable (ullong-integerp ullong-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;

(defruled sllong-integerp-alt-def
  :short "Alternative definition of @(tsee sllong-integerp) as integer range."
  (equal (sllong-integerp x)
         (and (integerp x)
              (<= (sllong-min) x)
              (<= x (sllong-max))))
  :enable (sllong-integerp sllong-min sllong-max)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uchar
  :short "Fixtype of C @('unsigned char') values [C:6.2.5/6]."
  ((get acl2::ubyte8))
  :tag :uchar
  :layout :list
  :pred ucharp)

;;;;;;;;;;

(fty::deflist uchar-list
  :short "Fixtype of lists of C @('unsigned char') values."
  :elt-type uchar
  :true-listp t
  :elementp-of-nil nil
  :pred uchar-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod schar
  :short "Fixtype of C @('signed char') values [C:6.2.5/5]."
  ((get acl2::sbyte8))
  :tag :schar
  :layout :list
  :pred scharp)

;;;;;;;;;;

(fty::deflist schar-list
  :short "Fixtype of lists of C @('signed char') values."
  :elt-type schar
  :true-listp t
  :elementp-of-nil nil
  :pred schar-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ushort
  :short "Fixtype of C @('unsigned short') values."
  ((get ushort-integer))
  :tag :ushort
  :layout :list
  :pred ushortp)

;;;;;;;;;;

(fty::deflist ushort-list
  :short "Fixtype of lists of C @('unsigned short') values."
  :elt-type ushort
  :true-listp t
  :elementp-of-nil nil
  :pred ushort-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod sshort
  :short "Fixtype of C @('signed short') values."
  ((get sshort-integer))
  :tag :sshort
  :layout :list
  :pred sshortp)

;;;;;;;;;;

(fty::deflist sshort-list
  :short "Fixtype of lists of C @('signed short') values."
  :elt-type sshort
  :true-listp t
  :elementp-of-nil nil
  :pred sshort-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uint
  :short "Fixtype of C @('unsigned int') values."
  ((get uint-integer))
  :tag :uint
  :layout :list
  :pred uintp)

;;;;;;;;;;

(fty::deflist uint-list
  :short "Fixtype of lists of C @('unsigned int') values."
  :elt-type uint
  :true-listp t
  :elementp-of-nil nil
  :pred uint-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod sint
  :short "Fixtype of C @('signed int') values."
  ((get sint-integer))
  :tag :sint
  :layout :list
  :pred sintp)

;;;;;;;;;;

(fty::deflist sint-list
  :short "Fixtype of lists of C @('signed int') values."
  :elt-type sint
  :true-listp t
  :elementp-of-nil nil
  :pred sint-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ulong
  :short "Fixtype of C @('unsigned long') values."
  ((get ulong-integer))
  :tag :ulong
  :layout :list
  :pred ulongp)

;;;;;;;;;;

(fty::deflist ulong-list
  :short "Fixtype of lists of C @('unsigned long') values."
  :elt-type ulong
  :true-listp t
  :elementp-of-nil nil
  :pred ulong-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod slong
  :short "Fixtype of C @('signed long') values."
  ((get slong-integer))
  :tag :slong
  :layout :list
  :pred slongp)

;;;;;;;;;;

(fty::deflist slong-list
  :short "Fixtype of lists of C @('signed long') values."
  :elt-type slong
  :true-listp t
  :elementp-of-nil nil
  :pred slong-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ullong
  :short "Fixtype of C @('unsigned long long') values."
  ((get ullong-integer))
  :tag :ullong
  :layout :list
  :pred ullongp)

;;;;;;;;;;

(fty::deflist ullong-list
  :short "Fixtype of lists of C @('unsigned long long') values."
  :elt-type ullong
  :true-listp t
  :elementp-of-nil nil
  :pred ullong-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod sllong
  :short "Fixtype of C @('signed long long') values."
  ((get sllong-integer))
  :tag :sllong
  :layout :list
  :pred sllongp)

;;;;;;;;;;

(fty::deflist sllong-list
  :short "Fixtype of lists of C @('signed long long') values."
  :elt-type sllong
  :true-listp t
  :elementp-of-nil nil
  :pred sllong-listp)
