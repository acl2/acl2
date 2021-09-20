; Tests of prove-equivalence
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "equivalence-checker")
;;TODO: prove-equivalence should include these since it refers to them:
;(include-book "kestrel/bv/rotate" :dir :system) ;for LEFTROTATE32-OF-BVCHOP-5
(include-book "kestrel/axe/rules1" :dir :system) ;for UNSIGNED-BYTE-P-FORCED-OF-BV-ARRAY-READ
;(include-book "kestrel/axe/axe-rules" :dir :system) ;for BVAND-OF-CONSTANT-TIGHTEN-DAG-VERSION
;(include-book "kestrel/axe/bv-rules-axe" :dir :system) ;for BVCAT-TRIM-ARG2-DAG-ALL
;(include-book "kestrel/axe/axe-rules-mixed" :dir :system) ;for NOT-EQUAL-MAX-INT-WHEN-<=
;(include-book "kestrel/jvm/jvm-rules" :dir :system) ;for G-OF-G-OF-SET-FIELD-WHEN-PAIRS-DIFFERENT
;(include-book "jvm-rules-axe") ;for SET-FIELD-OF-SET-FIELD-REORDER-PAIRS
;todo: move these to equivalence-checker.lisp:
(include-book "kestrel/lists-light/firstn" :dir :system) ;for firstn-when-zp-cheap
(include-book "kestrel/lists-light/take" :dir :system)

(must-fail
 (prove-equivalence (dagify-term! '(bvplus '32 '1 x))
                    (dagify-term! '(bvplus '32 '2 x))))

(prove-equivalence (dagify-term! '(bvplus '32 '7 x))
                   (dagify-term! '(bvplus '32 x '7)))


(must-fail ;the dags have different vars
 (prove-equivalence (dagify-term! '(bvplus '32 x y))
                    (dagify-term! '(bvplus '32 x z))))

;TODO: Improve the error message here:
(must-fail
 (prove-equivalence (dagify-term! '(bvplus '32 x y))
                    (dagify-term! '(bvmult '32 x y))))

;try with terms instead of dags:
(prove-equivalence '(bvplus '32 '7 x)
                   '(bvplus '32 x '7))

; try with one term and one dag:
(prove-equivalence '(bvplus '32 '7 x)
                   (dagify-term! '(bvplus '32 x '7)))
