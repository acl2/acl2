; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/defrule" :dir :system)

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
                  x)))

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
