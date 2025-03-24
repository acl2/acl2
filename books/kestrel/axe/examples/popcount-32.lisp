; A simple Axe example involving popcount
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (uses-stp)

;; This book uses Axe to prove that the popcount_32 function (below) correctly
;; counts the number of 1 bits in its 32-bit argument, V.  For the
;; specification, we use the BVCOUNT function from the BV library.

(include-book "kestrel/axe/equivalence-checker" :dir :system) ;has skip-proofs (currently)
(include-book "kestrel/bv/bvcount" :dir :system)

;; A function to count the number of one bits in V.
;; This was lifted from an x86 binary (in ../x86/examples/popcount/popcount-32-proof.lisp)
;; but that doesn't matter here.
(defun popcount_32 (v)
  (slice 31 24
         (bvmult 32 16843009
                 (bvand 32 252645135
                        (bvplus 32
                                (bvplus 32
                                        (bvand 32 858993459
                                               (bvplus 32 v
                                                       (bvuminus 32
                                                                 (bvand 31 1431655765 (slice 31 1 v)))))
                                        (bvand 30 858993459
                                               (slice 31 2
                                                      (bvplus 32 v
                                                              (bvuminus 32
                                                                        (bvand 31 1431655765 (slice 31 1 v)))))))
                                (slice 31 4
                                       (bvplus 32
                                               (bvand 32 858993459
                                                      (bvplus 32 v
                                                              (bvuminus 32
                                                                        (bvand 31 1431655765 (slice 31 1 v)))))
                                               (bvand 30 858993459
                                                      (slice 31 2
                                                             (bvplus 32 v
                                                                     (bvuminus 32
                                                                               (bvand 31 1431655765 (slice 31 1 v)))))))))))))

;; Prove equivalence of popcount_32 and bvcount (which we take as the spec).
;; This combines the spec unrolling with the equivalence proof.
(prove-equal-with-axe '(popcount_32 v)
                      '(bvcount '32 v) ; spec
                      ;; Rules to open and unroll functions:
                      :extra-rules (append '(popcount_32
                                             bvcount-unroll
                                             bvcount-of-0-arg1)
                                           (core-rules-bv))
                      :types '((v . 32))
                      :initial-rule-sets nil ;; avoid bit-blasting
                      ;; :print t
                      )
