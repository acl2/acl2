; An Axe proof of an x86 implementation of TEA by unrolling
;
; Copyright (C) 2017-2022 Kestrel Technology, LLC
; Copyright (C) 2023 Kestrel Institute
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

(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system)

;; The spec for TEA encryption, and some rules about it:
(include-book "kestrel/crypto/tea/tea-rules" :dir :system)

;; Unroll the spec:
(acl2::unroll-spec-basic *tea-encrypt-spec*
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

; (depends-on "tea.macho64")

;; Lift the subroutine into logic:
;; Produces the DAG *tea*.
(def-unrolled tea
  "tea.macho64"
  :stack-slots 8
  :target "_encrypt"
  ;; todo: have the tool translate the items in the tuple:
  :output (:tuple (:mem32 (rdi x86)) ;extract v0
           (:mem32 (binary-+ '4 (rdi x86)))) ;extract v1
  ;; TODO: How much of this can we automate?
  ;; TODO: Can we just make stronger assumptions about things being loaded at concrete addresses?
  :assumptions '((canonical-address-p$inline (rdi x86))
                 (canonical-address-p$inline (binary-+ 7 (rdi x86))) ; first arg has 2 32-bit elements = 8 bytes
                 (canonical-address-p$inline (rsi x86))
                 (canonical-address-p$inline (binary-+ 15 (rsi x86))) ; second arg has 4 32-bit elements = 16 bytes

                 ;;disjointness of v and stack:
                 ;; TODO: Why does separate take the :r arguments?
                 (separate :r 8 (rdi x86)
                           :r 80 ;assuming 10 stack slots
                           (binary-+ -80 (rsp x86)))

                 ;;disjointness of k and stack:
                 (separate :r 16 (rsi x86)
                           :r 80 ;assuming 10 stack slots
                           (binary-+ -80 (rsp x86)))

                 ;;disjointness of v and code:
                 (separate :r 8 (rdi x86)
                           :r 651 text-offset)

                 ;; ;;disjointness of k and code (not needed, because k is not written):
                 ;; (separate :r 16 (rsi x86)
                 ;;           :r 651 text-offset)

                 ;;disjointness of return address and v:
                 (separate :r 8 (rsp x86)
                           :r 8 (rdi x86))

                 ;; introduce vars (todo: automate):

                 (equal (read 4 (rsi x86) x86)
                        ;; todo: check endianness:
                        (bvcat 8 key0 24
                               (bvcat 8
                                      key1 16
                                      (bvcat 8 key2 8 key3))))

                 (equal (read 4 (binary-+ 4 (rsi x86))
                              x86)
                        (bvcat 8
                               key4 24
                               (bvcat 8
                                      key5 16
                                      (bvcat 8 key6 8 key7))))

                 (equal (read 4 (binary-+ 8 (rsi x86)) x86)
                        (bvcat 8
                               key8 24
                               (bvcat 8
                                      key9 16
                                      (bvcat 8 key10 8 key11))))

                 (equal (read 4 (binary-+ 12 (rsi x86)) x86)
                        (bvcat 8 key12 24
                               (bvcat 8
                                      key13 16
                                      (bvcat 8 key14 8 key15))))

                 ;; Introduce vars for v:

                 (equal (read 4 (rdi x86) x86)
                        (bvcat 8 in0 24
                               (bvcat 8
                                      in1 16
                                      (bvcat 8 in2 8 in3))))
                 (equal (read 4 (binary-+ 4 (rdi x86)) x86)
                        (bvcat 8 in4 24
                               (bvcat 8
                                      in5 16
                                      (bvcat 8 in6 8 in7)))))
   :produce-function nil ; we only need the dag
   )

;; Prove the equivalence of the code and the spec:
(prove-equivalence *tea*
                   *tea-encrypt-spec*
                   :initial-rule-sets (list (make-axe-rules! (amazing-rules-bv) (w state))) ;don't bit-blast
                   :tactic :rewrite-and-sweep)
