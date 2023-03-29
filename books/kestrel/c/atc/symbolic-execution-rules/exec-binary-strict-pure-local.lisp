; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")

(include-book "../../representation/integer-operations")

(include-book "integers")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file is only included locally
; in the files that generate the rules for the binary operators.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "kestrel/arithmetic-light/expt" :dir :system)
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/arithmetic-light/truncate" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x)
                  x))
  :enable ifix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule truncate-lemma
  (implies (and (natp a)
                (natp b))
           (and (<= 0
                    (truncate a (expt 2 b)))
                (<= (truncate a (expt 2 b))
                    a)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled shl-values-to-shl-integer-values
  (implies (and (value-integerp x)
                (value-integerp y))
           (equal (shl-values x y)
                  (shl-integer-values (promote-value x)
                                      (promote-value y))))
  :enable shl-values)

(defruled shr-values-to-shr-integer-values
  (implies (and (value-integerp x)
                (value-integerp y))
           (equal (shr-values x y)
                  (shr-integer-values (promote-value x)
                                      (promote-value y))))
  :enable shr-values)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled integer-type-bits-when-type-sint
  (implies (equal type (type-sint))
           (equal (integer-type-bits type)
                  (int-bits)))
  :enable integer-type-bits)

(defruled integer-type-bits-when-type-uint
  (implies (equal type (type-uint))
           (equal (integer-type-bits type)
                  (int-bits)))
  :enable integer-type-bits)

(defruled integer-type-bits-when-type-slong
  (implies (equal type (type-slong))
           (equal (integer-type-bits type)
                  (long-bits)))
  :enable integer-type-bits)

(defruled integer-type-bits-when-type-ulong
  (implies (equal type (type-ulong))
           (equal (integer-type-bits type)
                  (long-bits)))
  :enable integer-type-bits)

(defruled integer-type-bits-when-type-sllong
  (implies (equal type (type-sllong))
           (equal (integer-type-bits type)
                  (llong-bits)))
  :enable integer-type-bits)

(defruled integer-type-bits-when-type-ullong
  (implies (equal type (type-ullong))
           (equal (integer-type-bits type)
                  (llong-bits)))
  :enable integer-type-bits)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::set-default-parents atc-symbolic-execution-rules)
