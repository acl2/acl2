; A proof of popcount_32
;
; Copyright (C) 2016-2026 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

; cert_param: (uses-stp)

;; This book lifts the functionality of popcount_32 into logic using the
;; Axe-based ARM32 lifter, and proves it equivalent to the spec.

(include-book "kestrel/axe/arm/portcullis" :dir :system)
(include-book "kestrel/axe/arm/unroller" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system) ;has skip-proofs
(include-book "kestrel/bv/bvcount" :dir :system) ; the spec

;; Despite the 64 in the .executable file name, this book only deals
;; with the 32-bit popcount routine.

;; (depends-on "popcount.arm32.elf32")

;; Lift the code into logic (1 second):
(def-unrolled popcount_32
  :executable "popcount.arm32.elf32"
  :target "popcount_32"
  :output :r0
  :extra-assumptions '((equal (reg 0 arm) v))
  ;:inputs ((v u32))
  )

;; Prove equivalence of the lifted code and the spec (3 seconds):
;; This combines the spec unrolling with the equivalence proof.
(prove-equal-with-axe '(popcount_32 v) ; lifted code
                      '(acl2::bvcount '32 v) ; spec
                      ;; Rules to open and unroll the spec:
                      :extra-rules (append '(popcount_32
                                             acl2::bvcount-unroll
                                             acl2::bvcount-of-0-arg1)
                                           (acl2::core-rules-bv))
                      :types '((v . 32))
                      ;; avoid bit-blasting:
                      :initial-rule-sets nil)
