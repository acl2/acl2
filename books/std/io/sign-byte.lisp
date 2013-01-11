;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(set-verify-guards-eagerness 2)

(defund sign-byte (x)
  (declare (type (unsigned-byte 8) x))
  (if (< x 128)
      x
    (- x 256)))

(local (in-theory (enable sign-byte)))

(defthm sign-byte-type
  (implies (integerp x)
           (integerp (sign-byte x)))
  :rule-classes ((:type-prescription) (:rewrite)))

(local (defun logbitp-equiv (i x y)
  (declare (xargs :guard (and (natp i)
                              (integerp x)
                              (integerp y))))
  (and (equal (logbitp i x) (logbitp i y))
       (or (zp i)
           (logbitp-equiv (1- i) x y)))))

(local (defthm logbitp-equiv-lemma
  (implies (and (logbitp-equiv n x y)
                (syntaxp (not (equal x y)))
                (integerp n)
                (<= 0 n)
                (integerp i)
                (<= 0 i)
                (<= i n))
           (equal (logbitp i y)
                  (logbitp i x)))
  :hints(("Goal" :in-theory (disable logbitp)))))

(local (defun test-sign-byte (i)
  (declare (type (unsigned-byte 8) i))
  (and (logbitp-equiv 7 i (sign-byte i))
       (or (zp i)
           (test-sign-byte (1- i))))))

(local (defthm test-sign-byte-lemma
  (implies (and (test-sign-byte n)
                (integerp n) (<= 0 n)
                (integerp i) (<= 0 i) (<= i n)
                (integerp k) (<= 0 k) (< k 8))
           (equal (logbitp k (sign-byte i))
                  (logbitp k i)))
  :hints(("Goal" :in-theory (disable logbitp)))))

(defthm sign-byte-bit-correct
  (implies (and (unsigned-byte-p 8 i)
                (integerp k)
                (<= 0 k)
                (< k 8))
           (equal (logbitp k (sign-byte i))
                  (logbitp k i)))
  :hints(("Goal" :use (:instance test-sign-byte-lemma (n 255)))))

(defthm sign-byte-range-correct
  (implies (unsigned-byte-p 8 i)
           (signed-byte-p 8 (sign-byte i))))

