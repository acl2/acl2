; An Axe proof of popcount_64
;
; Copyright (C) 2016-2026 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

; cert_param: (uses-stp)

;; This book lifts the functionality of popcount_64 into logic using the
;; Axe-based ARM32 lifter, and proves it equivalent to the spec.

(include-book "kestrel/axe/arm/unroller" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system) ;has skip-proofs
(include-book "kestrel/bv/bvcount" :dir :system) ; the spec

;; (depends-on "popcount.arm32.elf32")

;; Lift the code into logic (1 second):
(def-unrolled popcount_64
  :executable "popcount.arm32.elf32"
  :target "popcount_64"
  :output :r0
  :extra-rules '(arm::bigendian arm::havelpae)
  :monitor '(:debug)
  :produce-function nil ; just make the DAG
  ;; :inputs ((v u64))
  :extra-assumptions '((equal (reg 0 arm) (bvchop 32 v)) ;; the input comes in split between r0 and r1
                       (equal (reg 1 arm) (slice 63 32 v))
                       (unsigned-byte-p 64 v)
                       ;; LR disjoint from the area where the stack grows:
                       (disjoint-regions32p 4 (reg *lr* arm) 400 (bvplus 32 4294966896 (reg 13 arm)))))

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
