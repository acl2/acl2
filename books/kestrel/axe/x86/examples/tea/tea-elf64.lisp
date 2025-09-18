; An Axe proof of an x86 implementation of TEA by unrolling
;
; Copyright (C) 2017-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: COMPLETE

;; This file verifies an implementation of the TEA block cipher.  It lifts the
;; functionality of TEA into logic using the Axe-based x86 lifter and proves
;; the result equivalent to the spec.

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system)

;; The spec for TEA encryption, and some rules about it:
(include-book "kestrel/crypto/tea/tea-rules" :dir :system)

;; Unroll the spec:
;; Produces the DAG *tea-encrypt-spec*, with variables in0-in7 and key0-key15.
(unroll-spec-basic *tea-encrypt-spec*
                   ;; The expression to unroll (use TEA to encrypt IN using KEY),
                   `(bv-array-to-list '32
                                      (acl2::tea-encrypt (acl2::pack-tea-input ,(symbolic-list 'in 8))
                                                         (acl2::pack-tea-key ,(symbolic-list 'key 16))))
                   ;; Extra rules to use for unrolling:
                   :extra-rules (append '(bv-array-to-list
                                          acl2::bv-array-to-list-aux-base
                                          acl2::bv-array-to-list-aux-unroll)
                                        (acl2::tea-spec-rules))
                   ;; Type assumptions on the input variables:
                   :assumptions (append (symbolic-byte-assumptions 'in 8)
                                        (symbolic-byte-assumptions 'key 16)))

; (depends-on "tea.elf64")

;; Lift the x86 code for the encrypt function into logic:
;; Produces the DAG *tea*, with the same variables as *tea-encrypt-spec*.
(def-unrolled tea
  "tea.elf64"
  :target "encrypt"
  :stack-slots 9
  :inputs ((v u32[2]) (k u32[4]))
  :output (:tuple (:mem32 (rdi x86)) ;extract v0
           (:mem32 (binary-+ '4 (rdi x86)))) ;extract v1
  :extra-assumptions '(;; Introduce byte vars for v:
                       (equal v0 (bvcat2 8 in0 8 in1 8 in2 8 in3))
                       (equal v1 (bvcat2 8 in4 8 in5 8 in6 8 in7))
                       ;; Introduce byte vars for k:
                       (equal k0 (bvcat2 8 key0 8 key1 8 key2 8 key3))
                       (equal k1 (bvcat2 8 key4 8 key5 8 key6 8 key7))
                       (equal k2 (bvcat2 8 key8 8 key9 8 key10 8 key11))
                       (equal k3 (bvcat2 8 key12 8 key13 8 key14 8 key15)))
  :produce-function nil ; we only need the dag
  )

;; Prove the equivalence of the code and the spec:
(prove-equal-with-axe *tea*
                      *tea-encrypt-spec*
                      :initial-rule-sets (list (make-axe-rules! (amazing-rules-bv) (w state))) ;don't bit-blast
                      :tactic :rewrite)
