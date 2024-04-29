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
(include-book "rules1") ;for UNSIGNED-BYTE-P-FORCED-OF-BV-ARRAY-READ
;(include-book "axe-rules") ;for BVAND-OF-CONSTANT-TIGHTEN-DAG-VERSION
;(include-book "bv-rules-axe") ;for BVCAT-TRIM-ARG4-AXE-ALL
;(include-book "axe-rules-mixed") ;for NOT-EQUAL-MAX-INT-WHEN-<=
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
;Sweeping-and-merging should just fail with no types provided -- or infer types.
(must-fail
 (prove-equivalence (dagify-term! '(bvplus '32 x y))
                    (dagify-term! '(bvmult '32 x y))))

(must-fail
 (prove-equivalence (dagify-term! '(bvplus '32 x y))
                    (dagify-term! '(bvmult '32 x y))
                    :local nil))

;try with terms instead of dags:
(prove-equivalence '(bvplus '32 '7 x)
                   '(bvplus '32 x '7))

; try with one term and one dag:
(prove-equivalence '(bvplus '32 '7 x)
                   (dagify-term! '(bvplus '32 x '7)))

;; TODO: Currently fails because we don't get induced types for X and Y
;; (that requires a parent-array, and sweeping does not maintain one), and
;; we don't call the Axe prover because the DAG is pure.
;; (prove-equivalence '(bvand '32 x y)
;;                    '(bvand '32 y x)
;;                    ;; avoid proving it via rewriting:
;;                    :initial-rule-sets nil)

;; This does work, because the Axe Prover is called on the probably-constant top node:
;; But proper test cases are not really made.
(defun foo (x) x)
(defun bar (x) x)
(prove-equivalence '(bvand '32 (foo x) (bar y))
                   '(bvand '32 (bar y) (foo x))
                   :print t
                   ;; avoid proving it via rewriting:
                   :initial-rule-sets nil)

;; trying to make a bvif with an irrelevant branch
;; (prove-equivalence '(bvif 32 x (bvif x 32 y z) y)
;;                    '(bvchop 32 y)
;;                    :print t
;;                    :check-vars nil
;;                    ;; avoid proving it via rewriting:
;;                    :initial-rule-sets nil)

;; (prove-equivalence '(bvif 32 x (bvif x 32 y (foo z)) y)
;;                    '(bvchop 32 y)
;;                    :print t
;;                    :check-vars nil
;;                    ;; avoid proving it via rewriting:
;;                    :initial-rule-sets nil)
