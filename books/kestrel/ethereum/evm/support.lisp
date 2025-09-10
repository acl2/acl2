; Supporting material for the EVM model
;
; Copyright (C) 2019-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/bv/bool-to-bit" :dir :system)
(include-book "kestrel/bv/logext" :dir :system)

;(local (in-theory (disable acl2::mod-x-y-=-x+y-for-rationals)))

;dup in bv.lisp
;todo: factor this out
(DEFTHM ACL2::>-CONSTANT-WHEN-INTEGER-STRENGTHEN
  (IMPLIES (AND (SYNTAXP (QUOTEP ACL2::K))
                (SYNTAXP (ACL2::WANT-TO-STRENGTHEN (< ACL2::K ACL2::X)))
                (INTEGERP ACL2::K)
                (INTEGERP ACL2::X))
           (EQUAL (< ACL2::K ACL2::X)
                  (<= (+ 1 ACL2::K) ACL2::X))))


(defthm unsigned-byte-p-of-if
  (equal (unsigned-byte-p size (if test x y))
         (if test
             (unsigned-byte-p size x)
           (unsigned-byte-p size y))))


;; also in std
(local
  (defthm eqlable-listp-when-nat-listp
    (implies (nat-listp x)
             (eqlable-listp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Material from conversions-es.lisp:

;; Recognize a bit-vector of the given size
;; The only bv of size 0 is 0
(defund bvp (size x)
  (declare (xargs :guard t))
  (unsigned-byte-p (nfix size) x))

;; Recognize a signed integer of the given size
;; The only sint of size 0 is 0
(defund sintp (size x)
  (declare (xargs :guard t))
  (if (not (posp size))
      (equal x 0)
    (signed-byte-p size x)))

(defthm sintp-forward-to-integerp
  (implies (sintp size n)
           (integerp n))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable sintp))))

(defund bv-to-sint (size x)
  (declare (xargs :guard (and (natp size)
                              (bvp size x))
                  :guard-hints (("Goal" :in-theory (enable bvp)))))
  (if (not (posp size))
      0
    (logext size x)))

(defund sint-to-bv (size x)
  (declare (xargs :guard (and (natp size)
                              (sintp size x))))
  (bvchop size x))
