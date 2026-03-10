; Copyright (C) 2025 by Kestrel Institute
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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/bit-vectors/bitops" :dir :system))

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

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
      "The implementation is similar to @('acl2::fchecksum-obj') (see @(see
       acl2::checksum)) in how we collect input bytes for the hash while
       walking over the ACL2 object.")
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
  (declare (xargs :split-types t)
           (type (unsigned-byte 8) byte)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let* ((acc (data::u32-plus acc byte))
           (acc (data::u32-plus acc (data::u32-shl acc 10))))
      (data::u32-xor acc (data::u32-shr acc 6))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t jenkins-acc-byte)))

(defrule jenkins-acc-byte-type-prescription
  (natp (jenkins-acc-byte byte acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-byte)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following definitions are based closely on acl2::fchecksum-obj.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-character
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
          (jenkins-acc-character (the character (char str i)) acc))
      (mbe :logic (if (unsigned-byte-p 32 acc)
                      acc
                    0)
           :exec acc)))
  :measure (nfix (- len (nfix i)))
  :hints (("Goal" :in-theory (enable the-check))))

(in-theory (disable (:t jenkins-acc-string-index)))

(defrule jenkins-acc-string-index-type-prescription
  (natp (jenkins-acc-string-index str i len acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-string-index)

(define jenkins-acc-string
  ((str stringp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type string str)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let ((len (length str)))
      (declare (type unsigned-byte len))
      (mbe :logic
           (jenkins-acc-string-index str 0 len acc)
           :exec
           ;; Note: this check may be optimized-away by some compilers,
           ;; which may infer that the length must always be smaller than
           ;; this upper bound
           ;; (I believe based on COMMON-LISP:ARRAY-DIMENSION-LIMIT).
           (if (<= len #.data::*u-fixnum-max*)
               (jenkins-acc-string-index str 0 (data::the-u-fixnum len) acc)
             (non-exec (jenkins-acc-string-index str 0 len acc))))))
  :inline t)

(in-theory (disable (:t jenkins-acc-string)))

(defrule jenkins-acc-string-type-prescription
  (natp (jenkins-acc-string str acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-nat
  ((n natp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type unsigned-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (if (or (not (mbt (natp n)))
          (< n #.data::*u8-max*))
      (jenkins-acc-byte (the (unsigned-byte 8) n) acc)
    (jenkins-acc-nat (the unsigned-byte (ash n -8))
                     (jenkins-acc-byte (the (unsigned-byte 8)
                                         (logand n #.data::*u8-max*))
                                       acc)))
  :measure (nfix n)
  :hints (("Goal" :in-theory (enable the-check))))

(defrule jenkins-acc-nat-type-prescription
  (natp (jenkins-acc-nat n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-nat)

(define jenkins-acc-integer
  ((n integerp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type signed-byte n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (if (natp n)
        (jenkins-acc-nat n acc)
      (jenkins-acc-nat (the unsigned-byte (- n))
                       (jenkins-acc-byte 0 acc))))
  :inline t)

(in-theory (disable (:t jenkins-acc-integer)))

(defrule jenkins-acc-integer-type-prescription
  (natp (jenkins-acc-integer n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-integer)

(define jenkins-acc-rational
  ((n rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type rational n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-nat (denominator n)
                     (jenkins-acc-integer (numerator n)
                                          acc)))
  :inline t)

(in-theory (disable (:t jenkins-acc-rational)))

(defrule jenkins-acc-rational-type-prescription
  (natp (jenkins-acc-rational n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-rational)

(define jenkins-acc-complex-rational
  ((n complex-rationalp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type complex n)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-rational (imagpart n)
                          (jenkins-acc-rational (realpart n)
                                                acc)))
  :inline t)

(in-theory (disable (:t jenkins-acc-complex-rational)))

(defrule jenkins-acc-complex-rational-type-prescription
  (natp (jenkins-acc-complex-rational n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-complex-rational)

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

(in-theory (disable (:t jenkins-acc-acl2-number)))

(defrule jenkins-acc-acl2-number-type-prescription
  (natp (jenkins-acc-acl2-number n acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-acl2-number)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-symbol
  ((symbol symbolp)
   (acc (unsigned-byte-p 32 acc)))
  (declare (xargs :split-types t)
           (type symbol symbol)
           (type (unsigned-byte 32) acc))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-string (symbol-name symbol)
                        (jenkins-acc-string (symbol-package-name symbol)
                                            acc)))
  :inline t)

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
            (mbe :logic (if (unsigned-byte-p 32 acc)
                            acc
                          0)
                 :exec acc))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable atom))))

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

(in-theory (disable (:t jenkins-acc)))

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
