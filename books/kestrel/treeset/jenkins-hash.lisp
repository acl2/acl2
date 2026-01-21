; Copyright (C) 2025 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "sum-acl2-count-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "kestrel/strings-light/char" :dir :system))

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "sum-acl2-count"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jenkins-hash
  :parents (implementation)
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
    (xdoc::@def "jenkins-hash")
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

(defconst *u8-max*
  (- (expt 2 8) 1))

(defconst *u32-max*
  (- (expt 2 32) 1))

(defconst *u-fixnum-max*
  (- (expt 2 acl2::*fixnum-bits*) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define u32-+ (x y)
  (declare (type (unsigned-byte 32) x)
           (type (unsigned-byte 32) y)
           (xargs :type-prescription (natp (u32-+ x y)))
           (optimize (speed 3) (safety 0)))
  :returns (product (unsigned-byte-p 32 product))
  (the (unsigned-byte 32)
    (logand (+ x y)
            *u32-max*))
  :inline t)

(define u32-ash (i c)
  (declare (type (unsigned-byte 32) i)
           (type (integer -31 31) c)
           (xargs :type-prescription (natp (u32-ash i c)))
           (optimize (speed 3) (safety 0)))
  :returns (shift (unsigned-byte-p 32 shift))
  (the (unsigned-byte 32)
    (logand (ash i c)
            *u32-max*))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-byte (byte acc)
  (declare (type (unsigned-byte 8) byte)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-byte byte acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let* ((acc (u32-+ acc byte))
           (acc (u32-+ acc (u32-ash acc 10))))
      (logxor acc (u32-ash acc -6))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following definitions are based closely on acl2::fchecksum-obj.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-character (c acc)
  (declare (type character c)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-character c acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-byte (the (unsigned-byte 8)
                        (char-code c))
                      acc))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: use loop$ (here and elsewhere)
(define jenkins-acc-string-fixnum-index (str i len acc)
  :guard (and (<= i len)
              (equal len (length str)))
  (declare (type string str)
           (type #.*u-fixnum-type* i)
           (type #.*u-fixnum-type* len)
           (type (unsigned-byte 32) acc)
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((i (mbe :logic (nfix i)
                :exec i))
        (len (mbe :logic (nfix len)
                  :exec len)))
    ;; TODO: redundant?
    (declare (type #.*u-fixnum-type* i)
             (type #.*u-fixnum-type* len))
    (if (and (mbt (and (<= i len)
                       (<= len *u-fixnum-max*)))
             (< i len))
        (jenkins-acc-string-fixnum-index
          str
          (the #.*u-fixnum-type* (1+ i))
          len
          (jenkins-acc-character (the character (char str i)) acc))
      (mbe :logic (if (unsigned-byte-p 32 acc)
                      acc
                    0)
           :exec acc)))
  :measure (nfix (- len (nfix i)))
  :hints (("Goal" :in-theory (enable o-p
                                     o<
                                     o-finp
                                     nfix
                                     natp
                                     the-check))))

(defrule jenkins-acc-string-fixnum-index-type-prescription
  (natp (jenkins-acc-string-fixnum-index str i len acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-string-fixnum-index)

(define jenkins-acc-string-nonfixnum-index (str i len acc)
  :guard (and (<= i len)
              (equal len (length str)))
  (declare (type string str)
           (type unsigned-byte i)
           (type unsigned-byte len)
           (type (unsigned-byte 32) acc)
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((i (mbe :logic (nfix i)
                :exec i))
        (len (mbe :logic (nfix len)
                  :exec len)))
    ;; TODO: redundant?
    (declare (type unsigned-byte i)
             (type unsigned-byte len))
    (if (and (mbt (<= i len))
             (< i len))
        (jenkins-acc-string-nonfixnum-index
          str
          (the unsigned-byte (1+ i))
          len
          (jenkins-acc-character (the character (char str i)) acc))
      (mbe :logic (if (unsigned-byte-p 32 acc)
                      acc
                    0)
           :exec acc)))
  :measure (nfix (- len (nfix i)))
  :hints (("Goal" :in-theory (enable o-p
                                     o<
                                     o-finp
                                     nfix
                                     natp
                                     the-check))))

(defrule jenkins-acc-string-nonfixnum-index-type-prescription
  (natp (jenkins-acc-string-nonfixnum-index str i len acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-string-nonfixnum-index)

(define jenkins-acc-string
  (str acc)
  (declare (type string str)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-string str acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (let ((len (length str)))
      (declare (type unsigned-byte len))
      (if (<= len *u-fixnum-max*)
          (jenkins-acc-string-fixnum-index str 0 (the #.*u-fixnum-type* len) acc)
        (jenkins-acc-string-nonfixnum-index str 0 len acc))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-nat (n acc)
  (declare (type unsigned-byte n)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-nat n acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (if (or (not (mbt (natp n)))
          (< n *u8-max*))
      (jenkins-acc-byte (the (unsigned-byte 8) n) acc)
    (jenkins-acc-nat (the unsigned-byte (ash n -8))
                     (jenkins-acc-byte (the (unsigned-byte 8)
                                         (logand n *u8-max*))
                                       acc)))
  :measure (nfix n)
  :hints (("Goal" :in-theory (enable o-p
                                     o<
                                     o-finp
                                     nfix
                                     the-check))))

(define jenkins-acc-integer (n acc)
  (declare (type signed-byte n)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-integer n acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (if (natp n)
        (jenkins-acc-nat n acc)
      (jenkins-acc-nat (the unsigned-byte (- n))
                  (jenkins-acc-byte 0 acc))))
  :inline t)

(define jenkins-acc-rational (n acc)
  (declare (type rational n)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-rational n acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-nat (denominator n)
                (jenkins-acc-integer (numerator n)
                                acc)))
  :inline t)

(define jenkins-acc-complex-rational (n acc)
  (declare (type complex n)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-complex-rational n acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-rational (imagpart n)
                     (jenkins-acc-rational (realpart n)
                                      acc)))
  :inline t)

(define jenkins-acc-acl2-number (n acc)
  (declare (type number n)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-acl2-number n acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (cond ((integerp n)
           (jenkins-acc-integer (the signed-byte n) acc))
          ((rationalp n)
           (jenkins-acc-rational (the rational n) acc))
          (t (jenkins-acc-complex-rational (the complex n) acc))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-symbol
  (symbol acc)
  (declare (type symbol symbol)
           (type (unsigned-byte 32) acc)
           (xargs :type-prescription (natp (jenkins-acc-symbol symbol acc)))
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (the (unsigned-byte 32)
    (jenkins-acc-string (symbol-name symbol)
                   (jenkins-acc-string (symbol-package-name symbol)
                                  acc)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-acc-atom (x acc)
  (declare (type atom x)
           (type (unsigned-byte 32) acc)
           (optimize (speed 3) (safety 0)))
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
  :inline t)

(defrule jenkins-acc-atom-type-presciption
  (natp (jenkins-acc-atom list acc))
  :rule-classes :type-prescription
  :enable jenkins-acc-atom)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: loop$
;; TODO: Is this associative on cons? Hopefully not
(define jenkins-acc-true-list
  ((list true-listp)
   acc)
  (declare (type (or cons null) list)
           (type (unsigned-byte 32) acc)
           (optimize (speed 3) (safety 0)))
  :returns (acc$ (unsigned-byte-p 32 acc$))
  (let ((acc (mbe :logic (if (unsigned-byte-p 32 acc)
                             acc
                           0)
                  :exec acc)))
    (if (endp list)
        acc
      (let ((first (first list)))
        (if (consp first)
            (jenkins-acc-true-list (list* (car first) (cdr first) (rest list))
                                   (jenkins-acc-byte
                                     ;; We chose an arbitrary byte to represent
                                     ;; cons
                                     #x70
                                     acc))
          (jenkins-acc-true-list (rest list)
                                 (jenkins-acc-atom first acc))))))
  :measure (acl2::nat-list-measure
            (list (sum-acl2-count list)
                  (len list)))
  :hints (("Goal" :in-theory (enable sum-acl2-count))))

(defrule jenkins-acc-true-list-type-presciption
  (natp (jenkins-acc-true-list list acc))
  :rule-classes :type-prescription
  :induct t
  :enable jenkins-acc-true-list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jenkins-hash (x)
  (declare (xargs :type-prescription (natp (jenkins-hash x)))
           (optimize (speed 3) (safety 0)))
  :returns (hash (unsigned-byte-p 32 hash))
  ;; Avoid clash with XDOC topic
  :parents nil
  (the (unsigned-byte 32)
    (let* ((acc (the (unsigned-byte 32)
                  (jenkins-acc-true-list (list x) 0)))
           (acc (u32-+ acc (u32-ash acc 3)))
           (acc (the (unsigned-byte 32)
                  (logxor acc (u32-ash acc -11)))))
      (u32-+ acc (u32-ash acc 15)))))
