; A proof of popcount_32
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

; cert_param: (uses-stp)

;; STATUS: COMPLETE

;; This book lifts the functionality of popcount_32 into logic using the
;; Axe-based x86 lifter, and proves it equivalent to the spec.

(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system) ;has skip-proofs
(include-book "kestrel/bv/bvcount" :dir :system) ; the spec

;; Bring in the code (despite the 64 in the .executable file name, this book only deals
;; with the 32-bit popcount routine):
(acl2::defconst-x86 *popcount-macho-64.executable* "popcount-macho-64.executable") ; (depends-on "popcount-macho-64.executable")

;; Lift the code into logic (1 second):
(def-unrolled popcount_32 *popcount-macho-64.executable*
  :target "_popcount_32"
  :stack-slots 2
  :output (:register 0)
  ;; Introduce x as the input var:
  :assumptions '((equal (xr :rgf *rdi* x86) x)))

;; Prove equivalence of the lifted code and the spec (3 seconds):
(prove-equivalence '(popcount_32 x) ; lifted code
                   '(acl2::bvcount '32 x) ; spec
                    ;; Rules to open and unroll the spec:
                   :extra-rules (append '(popcount_32
                                          acl2::bvcount-unroll
                                          acl2::bvcount-of-0-arg1)
                                  (acl2::core-rules-bv))
                   :types '((x . 32))
                   ;; avoid bit-blasting:
                   :initial-rule-sets nil)
