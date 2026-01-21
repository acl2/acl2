; A model of the FixedSizeBitVectors theory
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: use an SMT package?  but that name is already taken

;; See https://smt-lib.org/theories-FixedSizeBitVectors.shtml

(include-book "ints") ; for ints-mod
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From https://smt-lib.org/theories-FixedSizeBitVectors.shtml ("an important
;; consequence of the above definition"):

(thm
  (implies (and (integerp m)
                (integerp n)
                (< 0 n))
           (and (<= 0 (ints-mod m n))
                (< (ints-mod m n) n))))

;; We model bit vectors not as functions from bit indices to bits but rather as
;; the corresponding natural numbers.

(defun bv2nat (m b)
  (declare (xargs :guard (and (unsigned-byte-p m b)
                              (posp m)))
           (ignore m))
  b)

;; todo: bv2int

(defun nat2bv (m n)
  (declare (xargs :guard (and (natp n)
                              (posp m))))
  (ints-mod n (expt 2 m)))

;; todo: show unique
(thm
  (implies (and (natp n)
                (posp m))
           (equal (bv2nat m (nat2bv m n))
                  (ints-mod n (expt 2 m)))))
