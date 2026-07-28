; Copyright (C) 2025-2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HASH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/fixnum" :dir :system)
(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/bit-vectors/bitops" :dir :system))

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(local (include-book "kestrel/strings-light/char" :dir :system))

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We don't seem to have good rules about logtail
(local (in-theory (disable acl2::right-shift-to-logtail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jenkins-one-at-a-time
  :parents (hashes)
  :short
  (xdoc::topstring
    "An implementation of "
    (xdoc::a
      :href
      "https://en.wikipedia.org/wiki/Jenkins_hash_function#one_at_a_time"
      "Jenkins one-at-a-time")
    "hash.")
  :long
  (xdoc::topstring
    (xdoc::p
      "This is a non-cryptographic hash function.")
    (xdoc::p
      "The hash is computed by folding a byte serialization of the ACL2 object
       through the Jenkins one-at-a-time accumulator. The map from objects to
       byte streams is designed to be injective (except that all bad atoms
       share one encoding), so that hash collisions arise only from the final
       32-bit compression:")
    (xdoc::ul
      (xdoc::li
        "Each object is prefixed with a byte identifying its type (cons,
         symbol, string, character, integer, rational, complex, or
         bad-atom).")
      (xdoc::li
        "Natural numbers are serialized as base-128 varints: little-endian
         groups of 7 bits, where the high bit of each byte indicates whether
         another byte follows. This form is self-delimiting. Integers are
         first mapped to naturals by interleaving the nonnegative and negative
         integers (0, -1, 1, -2, 2, ... map to 0, 1, 2, 3, 4, ...), the
         so-called ``zigzag'' encoding.")
      (xdoc::li
        "Strings are length-prefixed (the length as a varint) followed by
         their character codes.")
      (xdoc::li
        "Compound atoms serialize their parts in sequence: symbols as their
         package name and symbol name (each length-prefixed), rationals as
         numerator and denominator (self-delimiting varints), and complex
         numbers as their real and imaginary parts."))
    (xdoc::p
      "For large integers, the varint serialization is computed by recursively
       splitting the integer roughly in half (at a multiple of 7 bits), so
       that the work is @($O(k\\log(k))$) in the bit-length @($k$), rather
       than the @($O(k^2)$) which would result from extracting one group at a
       time.")
    (xdoc::@def "jenkins")
    (xdoc::section
      "References"
      (xdoc::ul
        (xdoc::li
          (xdoc::a
            :href
            "https://en.wikipedia.org/wiki/Jenkins_hash_function#one_at_a_time"
            "https://en.wikipedia.org/wiki/Jenkins_hash_function#one_at_a_time"))
        (xdoc::li
          (xdoc::a
            :href
            "https://burtleburtle.net/bob/hash/doobs.html"
            "https://burtleburtle.net/bob/hash/doobs.html")))))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The type tag bytes used by the serialization. Every atom (and cons)
;; contributes exactly one of these bytes before its contents, so that objects
;; of different types never share a byte stream.
;;   cons:     #x70
;;   symbol:   #x71
;;   string:   #x72
;;   char:     #x73
;;   integer:  #x74
;;   rational: #x75
;;   complex:  #x76
;;   bad-atom: #x77

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-byte
  ((byte (unsigned-byte-p 8 byte))
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type (unsigned-byte 8) byte)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let* ((acc (data::u32-plus acc byte))
           (acc (data::u32-plus acc (data::u32-shl acc 10))))
      (data::u32-xor acc (data::u32-shr acc 6))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-byte)))

(defrule jenkins-acc-byte-type-prescription
  (natp (jenkins-acc-byte byte acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-byte)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Natural numbers are serialized as little-endian base-128 varints: each byte
;; carries 7 bits of the number, and the high bit indicates whether another
;; byte follows. This encoding is self-delimiting, which makes the
;; serialization of compound atoms (rationals, symbols, etc.) injective.

(defrulel <-of-loghead-7-and-128-linear
  (< (acl2::loghead 7 x) 128)
  :rule-classes :linear
  :use (:instance acl2::unsigned-byte-p-of-loghead
                  (acl2::size1 7)
                  (acl2::size 7)
                  (acl2::i x))
  :enable unsigned-byte-p
  :disable acl2::unsigned-byte-p-of-loghead)

;; Serialize a "small" (fixnum-sized) natural as a varint.
(define jenkins-acc-varint-small
  ((n (unsigned-byte-p 56 n))
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type (unsigned-byte 56) n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((n (mbe :logic (lnfix n)
                :exec (the (unsigned-byte 56) n))))
    (if (< n 128)
        (jenkins-acc-byte (the (unsigned-byte 8) n) acc)
      (jenkins-acc-varint-small
        (the (unsigned-byte 56) (ash n -7))
        (jenkins-acc-byte (the (unsigned-byte 8)
                            (+ 128 (the (unsigned-byte 7)
                                     (acl2::loghead 7 n))))
                          acc))))
  :measure (nfix n))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-varint-small)))

(defrule jenkins-acc-varint-small-type-prescription
  (natp (jenkins-acc-varint-small n acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-varint-small)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize exactly m 7-bit groups of a "small" (fixnum-sized) natural, each
;; with the continuation bit set. This is used for the low portion of a large
;; number, whose continuation bits are all set because more significant groups
;; always follow.
(define jenkins-acc-varint-groups-small
  ((x (unsigned-byte-p 56 x))
   (m natp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type (unsigned-byte 56) x)
           (type unsigned-byte m)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((m (mbe :logic (lnfix m)
                :exec (the unsigned-byte m))))
    (if (equal m 0)
        (mbe :logic (if (unsigned-byte-p 32 acc)
                        acc
                      0)
             :exec acc)
      (jenkins-acc-varint-groups-small
        (the (unsigned-byte 56) (ash x -7))
        (1- m)
        (jenkins-acc-byte (the (unsigned-byte 8)
                            (+ 128 (the (unsigned-byte 7)
                                     (acl2::loghead 7 x))))
                          acc))))
  :measure (nfix m))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-varint-groups-small)))

(defrule jenkins-acc-varint-groups-small-type-prescription
  (natp (jenkins-acc-varint-groups-small x m acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-varint-groups-small)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize exactly m 7-bit groups of x, each with the continuation bit set.
;; Large inputs are split roughly in half (at a multiple of 7 bits) so that
;; bignums are processed in O(k log(k)) time rather than the O(k^2) which
;; would result from shifting the entire bignum for each group.
(define jenkins-acc-varint-groups
  ((x natp)
   (m natp)
   (acc (unsigned-byte-p 32 acc)))
  :guard (unsigned-byte-p (* 7 m) x)
  (declare (xargs :split-types t)
           (type unsigned-byte x)
           (type unsigned-byte m)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((x (mbe :logic (lnfix x)
                :exec (the unsigned-byte x)))
        (m (mbe :logic (lnfix m)
                :exec (the unsigned-byte m))))
    (if (<= m 8)
        (jenkins-acc-varint-groups-small x m acc)
      (let* ((m1 (floor m 2))
             (bits1 (* 7 m1)))
        (jenkins-acc-varint-groups
          (ash x (- bits1))
          (- m m1)
          (jenkins-acc-varint-groups (acl2::loghead bits1 x) m1 acc)))))
  :measure (nfix m)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2::right-shift-to-logtail
                                           fix))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-varint-groups)))

(defrule jenkins-acc-varint-groups-type-prescription
  (natp (jenkins-acc-varint-groups x m acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-varint-groups)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize a natural number as a varint. Small numbers are handled directly;
;; large numbers are split roughly in half (at a multiple of 7 bits), the low
;; groups (whose continuation bits are all set) are serialized with
;; jenkins-acc-varint-groups, and the process recurs on the high part.
(define jenkins-acc-nat
  ((n natp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type unsigned-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((n (mbe :logic (lnfix n)
                :exec (the unsigned-byte n))))
    (if (< n 72057594037927936) ;; (expt 2 56)
        (jenkins-acc-varint-small n acc)
      (let* ((m1 (floor (integer-length n) 14))
             (bits1 (* 7 m1)))
        (jenkins-acc-nat
          (ash n (- bits1))
          (jenkins-acc-varint-groups (acl2::loghead bits1 n) m1 acc)))))
  :measure (nfix (integer-length n))
  :hints (("Goal" :in-theory (e/d (acl2::right-shift-to-logtail
                                   fix
                                   nfix)
                                  (acl2::<-of-integer-length-arg2))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2::right-shift-to-logtail
                                           fix))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-nat)))

(defrule jenkins-acc-nat-type-prescription
  (natp (jenkins-acc-nat n acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize an integer as a varint via the zigzag encoding
;; (0, -1, 1, -2, 2, ... maps to 0, 1, 2, 3, 4, ...).
(define jenkins-acc-integer-contents
  ((n integerp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type signed-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-nat (the unsigned-byte
                       (if (< n 0)
                           (+ -1 (* -2 n))
                         (* 2 n)))
                     acc))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-integer-contents)))

(defrule jenkins-acc-integer-contents-type-prescription
  (natp (jenkins-acc-integer-contents n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-integer-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-integer
  ((n integerp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type signed-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-integer-contents n (jenkins-acc-byte #x74 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-integer)))

(defrule jenkins-acc-integer-type-prescription
  (natp (jenkins-acc-integer n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-integer)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize a rational as its numerator (zigzag varint) followed by its
;; denominator (varint). Both parts are self-delimiting, so the pair is
;; unambiguous.
(define jenkins-acc-rational-contents
  ((n rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type rational n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-nat (denominator n)
                     (jenkins-acc-integer-contents (numerator n)
                                                   acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-rational-contents)))

(defrule jenkins-acc-rational-contents-type-prescription
  (natp (jenkins-acc-rational-contents n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-rational-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-rational
  ((n rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type rational n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-rational-contents n (jenkins-acc-byte #x75 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-rational)))

(defrule jenkins-acc-rational-type-prescription
  (natp (jenkins-acc-rational n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-rational)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-complex-rational
  ((n complex-rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type complex n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-rational-contents (imagpart n)
                                   (jenkins-acc-rational-contents
                                     (realpart n)
                                     (jenkins-acc-byte #x76 acc))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-complex-rational)))

(defrule jenkins-acc-complex-rational-type-prescription
  (natp (jenkins-acc-complex-rational n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-complex-rational)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-acl2-number
  ((n acl2-numberp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type number n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (cond ((integerp n)
           (jenkins-acc-integer (the signed-byte n) acc))
          ((rationalp n)
           (jenkins-acc-rational (the rational n) acc))
          (t (jenkins-acc-complex-rational (the complex n) acc))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-acl2-number)))

(defrule jenkins-acc-acl2-number-type-prescription
  (natp (jenkins-acc-acl2-number n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-acl2-number)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The character code alone, without a type tag. Used for the characters of a
;; string, which are delimited by the string's length prefix.
(define jenkins-acc-character-contents
  ((c characterp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type character c)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-byte (the (unsigned-byte 8)
                        (char-code c))
                      acc))
  :inline t
  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p
                                           integer-range-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-character-contents)))

(defrule jenkins-acc-character-contents-type-prescription
  (natp (jenkins-acc-character-contents c acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-character-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-character
  ((c characterp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type character c)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-character-contents c (jenkins-acc-byte #x73 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-character)))

(defrule jenkins-acc-character-type-prescription
  (natp (jenkins-acc-character c acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-character)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: use loop$
(define jenkins-acc-string-index
  ((str stringp)
   (i (unsigned-byte-p data::*fixnum-bits* i))
   (len (unsigned-byte-p data::*fixnum-bits* len))
   (acc (unsigned-byte-p 32 acc)))
  :guard (mbe :logic (and (<= i len)
                          (equal len (length str)))
              :exec (and (<= (data::the-u-fixnum i)
                             (data::the-u-fixnum len))
                         (equal (data::the-u-fixnum len)
                                (length (the string str)))))
  (declare (xargs :split-types t)
           (type string str)
           (type #.data::*u-fixnum-type* i len)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((i (mbe :logic (nfix i)
                :exec i))
        (len (mbe :logic (nfix len)
                  :exec len)))
    ;; TODO: redundant?
    (declare (type #.data::*u-fixnum-type* i len))
    (if (and (mbt (and (<= i len)
                       (<= len #.data::*u-fixnum-max*)))
             (< i len))
        (jenkins-acc-string-index
          str
          (the #.data::*u-fixnum-type* (1+ i))
          len
          (jenkins-acc-character-contents (the character (char str i)) acc))
      (mbe :logic (if (unsigned-byte-p 32 acc)
                      acc
                    0)
           :exec acc)))
  :measure (nfix (- len (nfix i)))
  :hints (("Goal" :in-theory (enable acl2::the-check))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-string-index)))

(defrule jenkins-acc-string-index-type-prescription
  (natp (jenkins-acc-string-index str i len acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-string-index)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The string's length (as a varint) followed by its character codes, without
;; a type tag. Used for the package and name strings of a symbol.
(define jenkins-acc-string-contents
  ((str stringp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type string str)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let ((len (length str)))
      (declare (type unsigned-byte len))
      (let ((acc (jenkins-acc-nat len acc)))
        (declare (type (unsigned-byte 32) acc))
        (mbe :logic (jenkins-acc-string-index str 0 len acc)
             :exec
             ;; Note: this check may be optimized-away by some compilers,
             ;; which may infer that the length must always be smaller than
             ;; this upper bound
             ;; (I believe based on COMMON-LISP:ARRAY-DIMENSION-LIMIT).
             (if (<= len #.data::*u-fixnum-max*)
                 (jenkins-acc-string-index str 0 (data::the-u-fixnum len) acc)
               (non-exec (jenkins-acc-string-index str 0 len acc)))))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-string-contents)))

(defrule jenkins-acc-string-contents-type-prescription
  (natp (jenkins-acc-string-contents str acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-string-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-string
  ((str stringp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type string str)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-string-contents str (jenkins-acc-byte #x72 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-string)))

(defrule jenkins-acc-string-type-prescription
  (natp (jenkins-acc-string str acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-symbol
  ((symbol symbolp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type symbol symbol)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-string-contents
      (symbol-name symbol)
      (jenkins-acc-string-contents
        (symbol-package-name symbol)
        (jenkins-acc-byte #x71 acc))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-symbol)))

(defrule jenkins-acc-symbol-type-prescription
  (natp (jenkins-acc-symbol symbol acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-symbol)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-atom
  (x
   (acc (unsigned-byte-p 32 acc)))
  :guard (mbe :logic (not (consp x))
              :exec (atom x))
  (declare (xargs :split-types t)
           (type atom x)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (cond ((symbolp x)
           (jenkins-acc-symbol x acc))
          ((acl2-numberp x)
           (jenkins-acc-acl2-number x acc))
          ((stringp x)
           (jenkins-acc-string x acc))
          ((characterp x)
           (jenkins-acc-character x acc))
          (t ;; bad-atom
            (jenkins-acc-byte #x77 acc))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable atom))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-atom)))

(defrule jenkins-acc-atom-type-presciption
  (natp (jenkins-acc-atom list acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-atom)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc
  (x
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((acc (mbe :logic (if (unsigned-byte-p 32 acc)
                             acc
                           0)
                  :exec acc)))
    (if (consp x)
        (jenkins-acc (cdr x)
                     (jenkins-acc (car x)
                                  (jenkins-acc-byte
                                    ;; We chose an arbitrary byte to represent
                                    ;; cons
                                    #x70
                                    acc)))
      (jenkins-acc-atom x acc)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc)))

(defrule jenkins-acc-type-presciption
  (natp (jenkins-acc x acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins (x)
  :parents (jenkins-one-at-a-time)
  :returns (hash (unsigned-byte-p 32 hash))
  (the (unsigned-byte 32)
    (let* ((acc (the (unsigned-byte 32)
                  (jenkins-acc x 0)))
           (acc (data::u32-plus acc (data::u32-shl acc 3)))
           (acc (data::u32-xor acc (data::u32-shr acc 11))))
      (data::u32-plus acc (data::u32-shl acc 15)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins)))

(defrule jenkins-type-presciption
  (natp (jenkins x))
  :rule-classes :type-prescription
  :enable jenkins)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-jenkins
  ((x acl2-numberp))
  (mbe :logic (jenkins x)
       :exec (the (unsigned-byte 32)
               (let* ((acc (the (unsigned-byte 32)
                             (jenkins-acc-acl2-number x 0)))
                      (acc (data::u32-plus acc (data::u32-shl acc 3)))
                      (acc (data::u32-xor acc (data::u32-shr acc 11))))
                 (data::u32-plus acc (data::u32-shl acc 15)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable jenkins
                                           jenkins-acc
                                           jenkins-acc-atom))))

(define symbol-jenkins
  ((x symbolp))
  (mbe :logic (jenkins x)
       :exec (the (unsigned-byte 32)
               (let* ((acc (the (unsigned-byte 32)
                             (jenkins-acc-symbol x 0)))
                      (acc (data::u32-plus acc (data::u32-shl acc 3)))
                      (acc (data::u32-xor acc (data::u32-shr acc 11))))
                 (data::u32-plus acc (data::u32-shl acc 15)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable jenkins
                                           jenkins-acc
                                           jenkins-acc-atom))))

(define eqlable-jenkins
  ((x eqlablep))
  (mbe :logic (jenkins x)
       :exec (the (unsigned-byte 32)
               (let* ((acc (the (unsigned-byte 32)
                             (cond ((symbolp x)
                                    (jenkins-acc-symbol x 0))
                                   ((acl2-numberp x)
                                    (jenkins-acc-acl2-number x 0))
                                   (t
                                    (jenkins-acc-character x 0)))))
                      (acc (data::u32-plus acc (data::u32-shl acc 3)))
                      (acc (data::u32-xor acc (data::u32-shr acc 11))))
                 (data::u32-plus acc (data::u32-shl acc 15)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable jenkins
                                           jenkins-acc
                                           jenkins-acc-atom))))
