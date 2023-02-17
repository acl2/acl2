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

(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))

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

(defrule truncate-lemma
  (implies (and (natp a)
                (natp b))
           (and (<= 0
                    (truncate a (expt 2 b)))
                (<= (truncate a (expt 2 b))
                    a)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::set-default-parents atc-symbolic-execution-rules)
