; An Axe proof of popcount_64
;
; Copyright (C) 2016-2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

; cert_param: (uses-stp)

;; STATUS: COMPLETE

;; This book lifts the functionality of popcount_64 into logic using the
;; Axe-based x86 lifter, and proves it equivalent to the spec.

(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system) ;has skip-proofs
(include-book "kestrel/bv/bvcount" :dir :system) ; the spec

;; (depends-on "popcount-macho-64.executable")

;; Lift the code into logic (1 second):
(def-unrolled popcount_64 "popcount-macho-64.executable"
  :target "_popcount_64"
  :stack-slots 8
  :output :rax
  :produce-function nil ; just make the DAG
  :inputs ((v u64)))

;; Unroll the spec:
(acl2::unroll-spec-basic *popcount-64-spec*
                         '(acl2::bvcount '64 v)
                         ;; Extra rules to use for unrolling:
                         :extra-rules (append '(acl2::bvcount-unroll
                                                acl2::bvcount-of-0-arg1)))

;; Prove equivalence of the lifted code and the spec:
(prove-equal-with-axe *popcount_64* ; lifted code
                      *popcount-64-spec*
                      :max-conflicts 4000000
                      :types '((v . 64))
                      ;; avoid bit-blasting:
                      :initial-rule-sets nil)
