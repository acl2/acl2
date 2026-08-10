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

(include-book "to-bytes")

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/fixnum" :dir :system)
(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "generic-fold"))

(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/bit-vectors/bitops" :dir :system))

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

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
      "The hash is logically @(tsee jenkins-bytes) applied to the @(see
       serialization) of the ACL2 object; see that topic for the encoding.
       Since the serialization is injective (except that all bad atoms share
       one encoding), hash collisions arise only from the final 32-bit
       compression. In execution, a single fused pass walks the object
       directly, without constructing the byte list.")
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

(define jenkins-acc-byte
  ((byte (unsigned-byte-p 8 byte))
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type (unsigned-byte 8) byte)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let* ((acc (data::u32-plus acc byte))
           (acc (data::u32-plus acc (data::u32-shl acc 10))))
      (data::u32-xor acc (data::u32-shr acc 6))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-byte-type-prescription
  (natp (jenkins-acc-byte byte acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-byte)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The accumulator folded over an explicit byte list. This is the reference
;; against which the fused jenkins-acc-* functions below are specified: each
;; is intended to be equal to jenkins-acc-bytes of the corresponding
;; serialization (see the serialization topic).
(define jenkins-acc-bytes
  ((bytes byte-listp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$)
                 :hints (("Goal" :induct t)))
  (if (endp bytes)
      (mbe :logic (if (unsigned-byte-p 32 acc)
                      acc
                    0)
           :exec acc)
    (jenkins-acc-bytes
      (cdr bytes)
      (jenkins-acc-byte (the (unsigned-byte 8) (car bytes)) acc))))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-bytes-type-prescription
  (natp (jenkins-acc-bytes bytes acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-bytes)

;; The step function does not distinguish a non-u32 accumulator from its
;; coercion to 0. This discharges the state-fix constraint when functionally
;; instantiating the generic fold theorems (see generic-fold).
(defruledl jenkins-acc-byte-when-not-unsigned-byte-p-32
  (implies (not (unsigned-byte-p 32 acc))
           (equal (jenkins-acc-byte byte acc)
                  (jenkins-acc-byte byte 0)))
  :enable (jenkins-acc-byte
           data::u32-plus$inline))

(defrule jenkins-acc-bytes-of-append
  (equal (jenkins-acc-bytes (append x y) acc)
         (jenkins-acc-bytes y (jenkins-acc-bytes x acc)))
  :use (:instance
         (:functional-instance update-bytes-of-append
                               (statep (lambda (st)
                                         (unsigned-byte-p 32 st)))
                               (state-fix (lambda (st)
                                            (if (unsigned-byte-p 32 st)
                                                st
                                              0)))
                               (update-byte (lambda (st byte)
                                              (jenkins-acc-byte byte st)))
                               (update-bytes (lambda (st bytes)
                                               (jenkins-acc-bytes bytes st))))
         (st acc))
  :enable (jenkins-acc-bytes
           jenkins-acc-byte-when-not-unsigned-byte-p-32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Natural numbers are serialized as unsigned LEB128: little-endian, each byte
;; carries 7 bits of the number, and the high bit indicates whether another
;; byte follows. This encoding is self-delimiting, which makes the
;; serialization of compound atoms (rationals, symbols, etc.) injective.

(defrulel <-of-loghead-7-and-128-linear
  (< (loghead 7 x) 128)
  :rule-classes :linear
  :use (:instance acl2::unsigned-byte-p-of-loghead
                  (acl2::size1 7)
                  (acl2::size 7)
                  (acl2::i x))
  :disable acl2::unsigned-byte-p-of-loghead)

;; Serialize a "small" (fixnum-sized) natural in LEB128 form.
;;
;; The width 56 = 7 * 8 is the largest whole number of 7-bit groups that fits
;; within data::*fixnum-bits* (61) on all supported hosts. Keeping the small
;; cases to whole groups lets the divide-and-conquer split only at group
;; boundaries, and keeping them within fixnum range makes the shifts in these
;; leaf loops register operations.
(define jenkins-acc-leb128-small
  ((n (unsigned-byte-p 56 n))
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type (unsigned-byte 56) n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((n (mbe :logic (lnfix n)
                :exec (the (unsigned-byte 56) n))))
    (if (< n 128)
        (jenkins-acc-byte (the (unsigned-byte 8) n) acc)
      (jenkins-acc-leb128-small
        (the (unsigned-byte 56) (ash n -7))
        (jenkins-acc-byte (the (unsigned-byte 8)
                            (+ 128 (the (unsigned-byte 7)
                                     (loghead 7 n))))
                          acc))))
  :measure (nfix n))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-leb128-small-type-prescription
  (natp (jenkins-acc-leb128-small n acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-leb128-small)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize exactly m 7-bit groups of a "small" (fixnum-sized) natural, each
;; with the continuation bit set. This is used for the low portion of a large
;; number, whose continuation bits are all set because more significant groups
;; always follow.
(define jenkins-acc-leb128-groups-small
  ((x (unsigned-byte-p 56 x))
   (m natp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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
      (jenkins-acc-leb128-groups-small
        (the (unsigned-byte 56) (ash x -7))
        (1- m)
        (jenkins-acc-byte (the (unsigned-byte 8)
                            (+ 128 (the (unsigned-byte 7)
                                     (loghead 7 x))))
                          acc))))
  :measure (nfix m))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-leb128-groups-small-type-prescription
  (natp (jenkins-acc-leb128-groups-small x m acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-leb128-groups-small)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize exactly m 7-bit groups of x, each with the continuation bit set.
;; Large inputs are split roughly in half (at a multiple of 7 bits) so that
;; bignums are processed in O(k log(k)) time rather than the O(k^2) which
;; would result from shifting the entire bignum for each group.
(define jenkins-acc-leb128-groups
  ((x natp)
   (m natp)
   (acc (unsigned-byte-p 32 acc)))
  :guard (unsigned-byte-p (* 7 m) x)
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type unsigned-byte x)
           (type unsigned-byte m)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((x (mbe :logic (lnfix x)
                :exec (the unsigned-byte x)))
        (m (mbe :logic (lnfix m)
                :exec (the unsigned-byte m))))
    (if (<= m 8) ;; 8 groups = 56 bits; see jenkins-acc-leb128-small
        (jenkins-acc-leb128-groups-small x m acc)
      (let* ((m1 (floor m 2))
             (bits1 (* 7 m1)))
        (jenkins-acc-leb128-groups
          (ash x (- bits1))
          (- m m1)
          (jenkins-acc-leb128-groups (loghead bits1 x) m1 acc)))))
  :measure (nfix m)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2::right-shift-to-logtail
                                           fix))))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-leb128-groups-type-prescription
  (natp (jenkins-acc-leb128-groups x m acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-leb128-groups)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize a natural number in LEB128 form. Small numbers are handled
;; directly;
;; large numbers are split roughly in half (at a multiple of 7 bits), the low
;; groups (whose continuation bits are all set) are serialized with
;; jenkins-acc-leb128-groups, and the process recurs on the high part.
(define jenkins-acc-nat
  ((n natp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type unsigned-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((n (mbe :logic (lnfix n)
                :exec (the unsigned-byte n))))
    (if (< n 72057594037927936) ;; (expt 2 56)
        (jenkins-acc-leb128-small n acc)
      (let* ((m1 (floor (integer-length n) 14))
             (bits1 (* 7 m1)))
        (jenkins-acc-nat
          (ash n (- bits1))
          (jenkins-acc-leb128-groups (loghead bits1 n) m1 acc)))))
  :measure (nfix (integer-length n))
  :hints (("Goal" :in-theory (e/d (acl2::right-shift-to-logtail
                                   fix
                                   nfix)
                                  (acl2::<-of-integer-length-arg2))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2::right-shift-to-logtail
                                           fix))))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-nat-type-prescription
  (natp (jenkins-acc-nat n acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize an integer in LEB128 form via the zigzag encoding
;; (0, -1, 1, -2, 2, ... maps to 0, 1, 2, 3, 4, ...).
(define jenkins-acc-integer-contents
  ((n integerp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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

(defrule jenkins-acc-integer-contents-type-prescription
  (natp (jenkins-acc-integer-contents n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-integer-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-integer
  ((n integerp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type signed-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-integer-contents n (jenkins-acc-byte #x74 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-integer-type-prescription
  (natp (jenkins-acc-integer n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-integer)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize a rational as its numerator (zigzag LEB128) followed by its
;; denominator (LEB128). Both parts are self-delimiting, so the pair is
;; unambiguous.
(define jenkins-acc-rational-contents
  ((n rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type rational n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-nat (denominator n)
                     (jenkins-acc-integer-contents (numerator n)
                                                   acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-rational-contents-type-prescription
  (natp (jenkins-acc-rational-contents n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-rational-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-rational
  ((n rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type rational n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-rational-contents n (jenkins-acc-byte #x75 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-rational-type-prescription
  (natp (jenkins-acc-rational n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-rational)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-complex-rational
  ((n complex-rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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

(defrule jenkins-acc-complex-rational-type-prescription
  (natp (jenkins-acc-complex-rational n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-complex-rational)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-acl2-number
  ((n acl2-numberp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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
  (declare (xargs :split-types t
                  :type-prescription :none)
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

(defrule jenkins-acc-character-contents-type-prescription
  (natp (jenkins-acc-character-contents c acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-character-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-character
  ((c characterp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type character c)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-character-contents c (jenkins-acc-byte #x73 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-character-type-prescription
  (natp (jenkins-acc-character c acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-character)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type string str)
           (type #.data::*u-fixnum-type* i len)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((i (mbe :logic (nfix i)
                :exec i))
        (len (mbe :logic (nfix len)
                  :exec len)))
    (declare (type #.data::*u-fixnum-type* i len))
    (if (and (mbt (<= i len))
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

(defrule jenkins-acc-string-index-type-prescription
  (natp (jenkins-acc-string-index str i len acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-string-index)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The string's length (in LEB128 form) followed by its character codes,
;; without
;; a type tag. Used for the package and name strings of a symbol.
(define jenkins-acc-string-contents
  ((str stringp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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

(defrule jenkins-acc-string-contents-type-prescription
  (natp (jenkins-acc-string-contents str acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-string-contents)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-string
  ((str stringp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type string str)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-string-contents str (jenkins-acc-byte #x72 acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-acc-string-type-prescription
  (natp (jenkins-acc-string str acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-symbol
  ((symbol symbolp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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
  (declare (xargs :split-types t
                  :type-prescription :none)
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

(defrule jenkins-acc-atom-type-presciption
  (natp (jenkins-acc-atom list acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-atom)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc
  (x
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
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

(defrule jenkins-acc-type-presciption
  (natp (jenkins-acc x acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each fused accumulator above equals jenkins-acc-bytes of the corresponding
;; serialization (see the serialization topic). These lemmas culminate in
;; jenkins-acc-becomes-jenkins-acc-bytes, which justifies the mbe in jenkins
;; below: the fused single-pass walk is logically the composition of the
;; serialization and the byte fold.

(defruled jenkins-acc-leb128-small-becomes-jenkins-acc-bytes
  (equal (jenkins-acc-leb128-small n acc)
         (jenkins-acc-bytes (nat-to-bytes n) acc))
  :induct (jenkins-acc-leb128-small n acc)
  :enable (jenkins-acc-leb128-small
           jenkins-acc-bytes
           nat-to-bytes))

(defruled jenkins-acc-leb128-groups-small-becomes-jenkins-acc-bytes
  (implies (natp x)
           (equal (jenkins-acc-leb128-groups-small x m acc)
                  (jenkins-acc-bytes (nat-to-leb128-groups x m) acc)))
  :induct (jenkins-acc-leb128-groups-small x m acc)
  :expand ((nat-to-leb128-groups x m))
  :enable (jenkins-acc-leb128-groups-small
           jenkins-acc-bytes))

;; The next two rules are the split lemmas from the serialization book,
;; instantiated at the implementation's own split points and guarded by
;; syntaxp to fire only on the induction variables (not on the halves they
;; introduce). This lets the inductive proofs below rewrite the
;; specification into alignment with the implementation without hints.

(defruledl nat-to-leb128-groups-split-in-half
  (implies (and (syntaxp (and (atom x) (atom m)))
                (natp x)
                (< 8 (nfix m)))
           (equal (nat-to-leb128-groups x m)
                  (append
                    (nat-to-leb128-groups (loghead (* 7 (floor (nfix m) 2)) x)
                                          (floor (nfix m) 2))
                    (nat-to-leb128-groups (logtail (* 7 (floor (nfix m) 2)) x)
                                          (- (nfix m) (floor (nfix m) 2))))))
  :use (:instance nat-to-leb128-groups-split
                  (n x)
                  (m (nfix m))
                  (m1 (floor (nfix m) 2))))

(defruledl nat-to-bytes-split-when-large
  (implies (and (syntaxp (atom n))
                (natp n)
                (<= 72057594037927936 n) ;; (expt 2 56); see jenkins-acc-nat
                (< (* 7 (floor (integer-length n) 14)) (integer-length n)))
           (equal (nat-to-bytes n)
                  (append
                    (nat-to-leb128-groups
                      (loghead (* 7 (floor (integer-length n) 14)) n)
                      (floor (integer-length n) 14))
                    (nat-to-bytes
                      (logtail (* 7 (floor (integer-length n) 14)) n)))))
  :use (:instance nat-to-bytes-split (m1 (floor (integer-length n) 14))))

(defruled jenkins-acc-leb128-groups-becomes-jenkins-acc-bytes
  (implies (natp x)
           (equal (jenkins-acc-leb128-groups x m acc)
                  (jenkins-acc-bytes (nat-to-leb128-groups x m) acc)))
  :induct (jenkins-acc-leb128-groups x m acc)
  :enable (jenkins-acc-leb128-groups
           jenkins-acc-leb128-groups-small-becomes-jenkins-acc-bytes
           nat-to-leb128-groups-split-in-half
           acl2::right-shift-to-logtail))

(defruled jenkins-acc-nat-becomes-jenkins-acc-bytes
  (implies (natp n)
           (equal (jenkins-acc-nat n acc)
                  (jenkins-acc-bytes (nat-to-bytes n) acc)))
  :induct (jenkins-acc-nat n acc)
  :enable (jenkins-acc-nat
           jenkins-acc-leb128-small-becomes-jenkins-acc-bytes
           jenkins-acc-leb128-groups-becomes-jenkins-acc-bytes
           nat-to-bytes-split-when-large
           acl2::right-shift-to-logtail))

(defruled jenkins-acc-integer-contents-becomes-jenkins-acc-bytes
  (implies (integerp n)
           (equal (jenkins-acc-integer-contents n acc)
                  (jenkins-acc-bytes (integer-contents-to-bytes n) acc)))
  :enable (jenkins-acc-integer-contents
           integer-contents-to-bytes
           jenkins-acc-nat-becomes-jenkins-acc-bytes))

(defruled jenkins-acc-integer-becomes-jenkins-acc-bytes
  (implies (integerp n)
           (equal (jenkins-acc-integer n acc)
                  (jenkins-acc-bytes (integer-to-bytes n) acc)))
  :enable (jenkins-acc-integer
           integer-to-bytes
           jenkins-acc-integer-contents-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-rational-contents-becomes-jenkins-acc-bytes
  (implies (rationalp n)
           (equal (jenkins-acc-rational-contents n acc)
                  (jenkins-acc-bytes (rational-contents-to-bytes n) acc)))
  :enable (jenkins-acc-rational-contents
           rational-contents-to-bytes
           jenkins-acc-integer-contents-becomes-jenkins-acc-bytes
           jenkins-acc-nat-becomes-jenkins-acc-bytes))

(defruled jenkins-acc-rational-becomes-jenkins-acc-bytes
  (implies (rationalp n)
           (equal (jenkins-acc-rational n acc)
                  (jenkins-acc-bytes (rational-to-bytes n) acc)))
  :enable (jenkins-acc-rational
           rational-to-bytes
           jenkins-acc-rational-contents-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-complex-rational-becomes-jenkins-acc-bytes
  (implies (complex-rationalp n)
           (equal (jenkins-acc-complex-rational n acc)
                  (jenkins-acc-bytes (complex-rational-to-bytes n) acc)))
  :enable (jenkins-acc-complex-rational
           complex-rational-to-bytes
           jenkins-acc-rational-contents-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-acl2-number-becomes-jenkins-acc-bytes
  (implies (acl2-numberp n)
           (equal (jenkins-acc-acl2-number n acc)
                  (jenkins-acc-bytes (acl2-number-to-bytes n) acc)))
  :enable (jenkins-acc-acl2-number
           acl2-number-to-bytes
           jenkins-acc-integer-becomes-jenkins-acc-bytes
           jenkins-acc-rational-becomes-jenkins-acc-bytes
           jenkins-acc-complex-rational-becomes-jenkins-acc-bytes))

(defruled jenkins-acc-character-contents-becomes-jenkins-acc-bytes
  (equal (jenkins-acc-character-contents c acc)
         (jenkins-acc-bytes (character-contents-to-bytes c) acc))
  :enable (jenkins-acc-character-contents
           character-contents-to-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-character-becomes-jenkins-acc-bytes
  (equal (jenkins-acc-character c acc)
         (jenkins-acc-bytes (character-to-bytes c) acc))
  :enable (jenkins-acc-character
           character-to-bytes
           jenkins-acc-character-contents-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-string-index-becomes-jenkins-acc-bytes
  (implies (and (stringp str)
                (natp i)
                (equal len (length str))
                (<= i len))
           (equal (jenkins-acc-string-index str i len acc)
                  (jenkins-acc-bytes
                    (characters-to-bytes (nthcdr i (coerce str 'list)))
                    acc)))
  :induct (jenkins-acc-string-index str i len acc)
  :enable (jenkins-acc-string-index
           jenkins-acc-bytes
           jenkins-acc-character-contents-becomes-jenkins-acc-bytes
           characters-to-bytes
           character-contents-to-bytes
           acl2::cdr-of-nthcdr
           char
           length))

(defruled jenkins-acc-string-contents-becomes-jenkins-acc-bytes
  (implies (stringp str)
           (equal (jenkins-acc-string-contents str acc)
                  (jenkins-acc-bytes (string-contents-to-bytes str) acc)))
  :enable (jenkins-acc-string-contents
           string-contents-to-bytes
           jenkins-acc-nat-becomes-jenkins-acc-bytes
           jenkins-acc-string-index-becomes-jenkins-acc-bytes))

(defruled jenkins-acc-string-becomes-jenkins-acc-bytes
  (implies (stringp str)
           (equal (jenkins-acc-string str acc)
                  (jenkins-acc-bytes (string-to-bytes str) acc)))
  :enable (jenkins-acc-string
           string-to-bytes
           jenkins-acc-string-contents-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-symbol-becomes-jenkins-acc-bytes
  (implies (symbolp symbol)
           (equal (jenkins-acc-symbol symbol acc)
                  (jenkins-acc-bytes (symbol-to-bytes symbol) acc)))
  :enable (jenkins-acc-symbol
           symbol-to-bytes
           jenkins-acc-string-contents-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

(defruled jenkins-acc-atom-becomes-jenkins-acc-bytes
  (implies (not (consp x))
           (equal (jenkins-acc-atom x acc)
                  (jenkins-acc-bytes (atom-to-bytes x) acc)))
  :enable (jenkins-acc-atom
           atom-to-bytes
           jenkins-acc-symbol-becomes-jenkins-acc-bytes
           jenkins-acc-acl2-number-becomes-jenkins-acc-bytes
           jenkins-acc-string-becomes-jenkins-acc-bytes
           jenkins-acc-character-becomes-jenkins-acc-bytes
           jenkins-acc-bytes))

;; Like the step function, the byte fold does not distinguish a non-u32
;; accumulator from its coercion to 0.
(defruledl jenkins-acc-bytes-when-not-unsigned-byte-p-32
  (implies (not (unsigned-byte-p 32 acc))
           (equal (jenkins-acc-bytes bytes acc)
                  (jenkins-acc-bytes bytes 0)))
  :expand ((jenkins-acc-bytes bytes acc)
           (jenkins-acc-bytes bytes 0))
  :enable jenkins-acc-byte-when-not-unsigned-byte-p-32)

(defruled jenkins-acc-becomes-jenkins-acc-bytes
  (equal (jenkins-acc x acc)
         (jenkins-acc-bytes (to-bytes x) acc))
  :induct (jenkins-acc x acc)
  :expand ((to-bytes x))
  :enable (jenkins-acc
           jenkins-acc-atom-becomes-jenkins-acc-bytes
           jenkins-acc-bytes
           jenkins-acc-bytes-when-not-unsigned-byte-p-32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The final avalanche, applied to the accumulator after all bytes have been
;; incorporated.
(define jenkins-finalize
  ((acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t
                  :type-prescription :none)
           (type (unsigned-byte 32) acc))
  :returns (hash (unsigned-byte-p 32 hash))
  (the (unsigned-byte 32)
    (let* ((acc (data::u32-plus acc (data::u32-shl acc 3)))
           (acc (data::u32-xor acc (data::u32-shr acc 11))))
      (data::u32-plus acc (data::u32-shl acc 15))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-finalize-type-prescription
  (natp (jenkins-finalize acc))
  :rule-classes :type-prescription
  :enable jenkins-finalize)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Jenkins one-at-a-time hash of an explicit byte list.
(define jenkins-bytes
  ((bytes byte-listp))
  (declare (xargs :type-prescription :none))
  :returns (hash (unsigned-byte-p 32 hash))
  (jenkins-finalize (jenkins-acc-bytes bytes 0)))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-bytes-type-prescription
  (natp (jenkins-bytes bytes))
  :rule-classes :type-prescription
  :enable jenkins-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins (x)
  (declare (xargs :type-prescription :none))
  :parents (jenkins-one-at-a-time)
  :returns (hash (unsigned-byte-p 32 hash))
  (mbe :logic (jenkins-bytes (to-bytes x))
       :exec (jenkins-finalize (jenkins-acc x 0)))
  :guard-hints
  (("Goal" :in-theory (enable jenkins-bytes
                              jenkins-acc-becomes-jenkins-acc-bytes))))

;;;;;;;;;;;;;;;;;;;;

(defrule jenkins-type-presciption
  (natp (jenkins x))
  :rule-classes :type-prescription
  :enable jenkins)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-jenkins
  ((x acl2-numberp))
  (mbe :logic (jenkins x)
       :exec (jenkins-finalize (jenkins-acc-acl2-number x 0)))
  :enabled t
  :guard-hints
  (("Goal"
    :in-theory (enable jenkins
                       jenkins-bytes
                       to-bytes
                       atom-to-bytes
                       jenkins-acc-acl2-number-becomes-jenkins-acc-bytes))))

(define symbol-jenkins
  ((x symbolp))
  (mbe :logic (jenkins x)
       :exec (jenkins-finalize (jenkins-acc-symbol x 0)))
  :enabled t
  :guard-hints
  (("Goal"
    :in-theory (enable jenkins
                       jenkins-bytes
                       to-bytes
                       atom-to-bytes
                       jenkins-acc-symbol-becomes-jenkins-acc-bytes))))

(define eqlable-jenkins
  ((x eqlablep))
  (mbe :logic (jenkins x)
       :exec (jenkins-finalize (cond ((symbolp x)
                                      (jenkins-acc-symbol x 0))
                                     ((acl2-numberp x)
                                      (jenkins-acc-acl2-number x 0))
                                     (t
                                      (jenkins-acc-character x 0)))))
  :enabled t
  :guard-hints
  (("Goal"
    :in-theory (enable jenkins
                       jenkins-bytes
                       to-bytes
                       atom-to-bytes
                       jenkins-acc-symbol-becomes-jenkins-acc-bytes
                       jenkins-acc-acl2-number-becomes-jenkins-acc-bytes
                       jenkins-acc-character-becomes-jenkins-acc-bytes))))
