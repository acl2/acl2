; A book that brings in all the pre-stp-rules
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: reduce what gets included here?
(include-book "rule-lists")
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)
(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "kestrel/arithmetic-light/plus" :dir :system) ; for INTEGERP-OF-+
(include-book "kestrel/arithmetic-light/minus" :dir :system) ; for INTEGERP-OF--
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvashr" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvuminus" :dir :system)
(include-book "kestrel/bv/rotate" :dir :system)
(include-book "kestrel/bv/bvnot" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(include-book "kestrel/bv/bitor" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/slice" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/sbvrem" :dir :system)
(include-book "kestrel/bv/repeatbit" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/rules" :dir :system) ; todo: for integerp-when-unsigned-byte-p-free
(include-book "kestrel/bv-arrays/bv-array-read-rules" :dir :system)
(include-book "basic-rules")
(include-book "bv-rules-axe0")
(include-book "bv-rules-axe")
(include-book "bv-array-rules-axe") ; not all are needed, but we need integerp-of-bv-array-read
(include-book "bv-intro-rules")

(ensure-rules-known (pre-stp-rules))
